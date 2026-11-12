# Current status and remaining work

This file is the sole entry point for known remaining work. Backlog triage does
not broaden the acceptance scope, semantics, theorem claims or test expectations.
See the [development guide](docs/development.md#check-commands) and
[test guide](tests/README.md) for check entry points, prerequisites and coverage.
Historical successes do not establish successful execution in the current checkout.

The acceptance scope includes common MIR, memory/Tree Borrows, Rust main startup
and exit, threads, synchronization, atomics, weak memory and data races. Finite
QA and general whole-machine proofs are separate goals. Overall completion and
the ability to verify arbitrary Rust are not claimed.

## Compiler material migration (in progress)

Runtime body providers now resolve exact identities through the execution-owned
BodyArena. Constructed Item instances select a unique ordinary raw MIR template
by physical definition and complete arguments; local layouts, frames, source
scopes and backtraces consume that identity. The obsolete lifecycle, scope and
backtrace result indexes are removed. Binder-free FnPtr AsPtr/FromPtr shims now
retain raw signatures, lang-item identities and source spans only; Lean constructs
their MIR, including for novel type/instance/body identities. Eight complete
pass-after rustc bodies and production corruption controls agree. HRTB FnPtr,
promoted bodies, general compiler shims and constructed shim ABI remain unresolved.
Novel-body controls exercise actual provider demand, dense identity reuse and
missing/ambiguous-source rejection.

Raw source environments retain explicit clauses, physical generic/predicate
parents, parameter sorts and trait identity. Lean assembles inherited obligations
after matching an impl head and for selected associated values; fully monomorphized
queries retain the empty ParamEnv. ADT Sized declaration entailment uses these
scopes. Legacy copied predicates are removed from producer, codecs and material
models. Fresh selection controls consume the canonical source scope and reject
its absence or the obsolete wire fields. Checked-alias, projection-bound and GAT
controls match independent rustc results. Region-only quantified obligations now
use query-local fresh universes, typed inference, scoped normalization and a
directional region-leak check in actual runtime selection. Eight complete rustc
comparisons distinguish four proven and four definite-no-solution results,
including static-only and repeated-region negatives. Missing-source, malformed
owner and mutated-oracle controls reject. Closed source type aliases now normalize
inside the active quantified universe; seven genuine alias-bearing goals agree
with rustc, including nested forall obligations. Raw RHS/own-clause placeholders,
missing source and a mutated static-only oracle reject. Quantified type/constant
assumptions, bound-dependent aliases, inferred outlives, general builtin candidates, specialization and
coinductive quantified goals remain unresolved.

Binder-free Item signatures can construct x86_64 Rust scalar/ZST FnAbi in the
same World from raw signatures and codegen/panic flags. Twenty complete compiler
comparisons cover abort/unwind policies, including constructed instances with
empty ABI catalogs. Covered direct-call, catalog and covariance collectors no
longer acquire FnAbi answers: ten complete keys each lose four explicit calls.
Unused unsupported generic arguments retain an exact residual domain. Thin
references additionally match forty complete rustc ABIs across optimization and
panic settings; each covered key eliminates four explicit FnAbi acquisitions.
Twenty additional complete ABIs exercise source-derived Freeze/Unpin branches
for ADT, array and tuple pointees, with the same four-call elimination per key.
An independent empty-catalog World constructs a novel array reference at both
optimization settings. Raw reference-policy absence and unsupported fat
references reject. Box/aggregate/foreign/other-target ABI and eager enumeration
remain unresolved. Thin raw-pointer and binder-free FnPtr scalars additionally pass
twenty complete rustc comparisons; all forty scalar/pointer comparisons also
cover constructed instances without result catalogs. A separate base world
constructs a new array, pointer and instance outside the source prefixes and
matches the complete compiler ABI.
Pattern Range, NotNull and signed Or layouts now
use raw recipes; six complete compiler comparisons and malformed controls pass,
with covered explicit canonical layout acquisition omitted. Raw single-variant
and empty enum declarations now construct twelve complete compiler layouts,
including a novel generic enum outside both type and constant prefixes. Five
repr/multivariant/unsized cases remain exact residuals; malformed recipes and
missing raw declarations reject. Tagged/niche/coroutine layouts remain unresolved.
Non-Value pattern endpoints still require CTFE. Structural pointer/reference/tuple/array/slice
covariance runs on World syntax: an independent 16-by-16 rustc matrix passes
with an empty answer catalog. Nominal variance and richer relations remain.

Scalar const-generic names and complete binder-free FnPtr syntax now enter the
runtime constructor, layout, normalization and printer paths. Nine fresh material
FnPtr identities normalize without result rows and agree with complete compiler
layouts. Raw default expressions drive trailing-default elision; five novel
default cases and missing-material controls pass. Backtrace names for local Items
use execution-owned keys, including three novel instances checked against rustc.
Region-only higher-ranked FnPtr construction now preserves whole binders through
normalization, flag traversal and printing. Nine novel types match 27 compiler
flags, 36 raw/normalized strings and complete pointer layouts. Eight actual
splatted-index boundary cases validate all header entry points. Unsupported
material child families retain their exact residual rows; constructed instances
cannot borrow a numerically colliding row. Type/constant binders, bound aliases,
verbose bound names, implementation/external paths and display fallbacks remain.

Structural type hashes now use the pinned StableHasher protocol over World
syntax, with covered eager hash acquisition omitted. Independent comparisons
cover 265 hasher vectors, 28 types and novel constructed types; missing-ID, fuel
and missing-residual controls reject. Full raw DefPathData, atomic StableCrateId
and optional typed generic headers replace partial paths and default markers.
Lean reconstructs DefPathHash; eighteen compiler comparisons include lifetime
namespaces, with exact bidirectional crate-identity join controls. Foreign types,
pointers and pairs match four typed compiler hashes, including novel identities
without material type rows. Raw ADT/variant/field identities, flags, representation,
constructors, discriminant declarations and visibility now determine ADT stable
hashes. Twenty-eight complete rustc type-hash comparisons cover nominal ADT and
FnDef syntax, arrays and recursive Value constants, including empty-prefix
reconstruction and malformed/missing-source controls. FnPtr/HRTB, dyn, aliases,
closures/coroutines and non-Value constant hashes, full validity and allocation
identity/dedup reconstruction remain unresolved. These comparisons do
not establish whole-compiler equivalence, query closure or all-choice guest safety.

Raw MIR constants distinguish Ty, Unevaluated and Val. Covered primitive
Ty(Value) operands and required constants are evaluated in the execution World
without exporter Const::eval/ValTree queries; five genuine compiler constants
each eliminate two explicit calls and match complete evaluated values. Required
TooGeneric constants fail before the first instruction and preserve the tested
frame/local/allocation state. Closed, argument-free FnDef values have a separate
ZST rule; generic/bound FnDef cases reject. Raw aggregate ValTrees additionally
evaluate six ZST and four uniquely scalar tuple/struct values in the same World,
matching complete compiler values/types/instances and removing two explicit
evaluation calls per value. Malformed roots, missing nodes/fields and fuel
exhaustion reject; allocation-bearing pair/reprC values remain exact residuals.
Unevaluated, allocation-bearing ValTrees and general CTFE/interning remain unresolved; no successful no-op stands
in for their evaluation.

The exact `DropGlue(_, None)` shim family now retains only instance identity and
raw source position; its raw declaration signature supplies types. Lean builds
the one-Return body on demand and retains the execution World. Five independent
pinned rustc body/interface comparisons pass, including tuple/reference cases;
a fresh source-demand test also rejects nontrivial drop glue and mixed material
fallback fields. The 834,375-byte no-op drop guest exits zero in Lean (cursor 316)
and same-prepared-TyCtxt Miri. Miri skips the no-op frame, so the guest alone does
not validate body construction; the separate demand/oracle tests do. Its body
row shrinks from 519 to 161 compact JSON bytes, while the whole artifact grows
from 534,788 bytes with added source material/schema. Evidence is recorded in
`scratch/abi-port/noop-drop-start-world.manifest.json`. Nontrivial drops and other
shim families remain separate work.

Ordinary binder-free, type-only generic source calls now execute from shared raw
MIR templates and resolve their symbolic callee in the same execution-owned
World. A fresh `generic-mir-call-start.rs` guest has four selected body references
to two templates (825,563 bytes); Lean finalized with exit 0 (choice cursor 320)
and same-prepared-TyCtxt Miri also exited zero. Removing its leaf instance ABI
row produces Unsupported at the actual call (cursor 54). The existing Item
instance graph and complete ABI query catalog remain explicit residuals; novel
instance/body/ABI graph construction is not implemented by this call slice.
Evidence: `scratch/abi-port/generic-mir-call-start-world.manifest.json` and
adjacent native/reference logs. These are finite examples, not a general proof.

The exporter-to-Lean compiler migration is incomplete. Lean now implements
structural `boxed_ty`, `builtin_deref`, `struct_tail_raw`, selected region-erased
alias-free normalization, trivial Freeze/Unpin/UnsafeUnpin rules, virtual generic
argument prefix rebasing, and the instance-kind caller-location rule from raw
definition attributes. The earlier algebraic ID scheme has been removed.
Current runtime providers use one execution-owned type/constant World with dense
appended IDs and structural constructor interning; generic MIR, field projection,
arrays, pointer/reference construction and queries share that universe. It stores
constructor syntax, not layouts or normalized query answers, and shares no cache
with another execution. The exporter no longer seeds mutable pointer/reference
result nodes. Current World integration passes the two novel-type native guests
below; its full build/audit gate is still being rerun.
Primitive scalar/never and tuple layouts are reconstructed from TyKind/raw tuple
recipes and the target; the tuple resolver uses the pinned univariant layout
algorithm. ADT needs-drop rules execute against raw definition-level destructor
and ManuallyDrop identity material, with covered answers omitted by the exporter.
Initial ArgAbi construction, covered x86_64 nonpointer scalar passing modes,
`fn_can_unwind`, and covered source-signature argument ordering/fixed counts run
in Lean from explicit material recipes/seeds. Rewritten or unsupported FnAbi
signatures still carry explicit residual counts and physical ABI query results.

Fresh finite comparisons with pinned rustc passed 3,559 structural/auto-trait
queries across 541 types, 23 caller-location decisions (both outcomes), four
virtual generic-rebase prefixes, 22 complete primitive and four complete array
layouts. Another 316 complete pointer/reference layouts matched the pinned
rustc oracle, including sized, str, slice and dynamic pointees. Source-extracted
component comparisons passed 54 initial/scalar ABI and 252 unwind decisions.
Mutated structural/caller/rebase oracle controls were rejected. These are finite
component checks, not a compiler equivalence proof. The full native runner and ImportMIR build passed 1,200 jobs after fixing old
provider references, recipe-width validation and an exhausted build filesystem.
One fresh 844,898-byte no_std guest passed same-prepared-TyCtxt Miri exit-zero and
Lean finalized exit-zero with choice cursor 348, including mutable references,
raw-pointer reads, tuples, array-to-slice coercion and a tracked helper. Its
nested novel type/array layout and identity checks also passed. A separate
81,231,642-byte std guest also passed frozen checkpoint `67e70f76` Lean execution:
finalized exit-zero, cursor 2038, no active frame, and completed leak checking,
matching its same-prepared-TyCtxt Miri exit-zero reference. One CPU-2 trial with
one Lean thread measured 5.182 s wall / 5.134 s child CPU, 540,640 KiB peak RSS,
0.14 s same-CPU steal, zero cgroup throttling and unchanged memory-event counters.
Frozen binary/input/source hashes remained unchanged. This single shared-host
trial is not a speedup claim; raw manifests and profiles are in ignored
`scratch/material-large-trial/`.
A fresh 875,896-byte `expected_ub` control reached Tree Borrows forbidden-read UB
at source line 18 in both same-TyCtxt Miri and the frozen Lean runner (cursor 69).
The exporter returned failure because Miri reported the expected UB, while Lean's
process exited zero with an explicit `undefined_behavior` terminal; neither is
counted as safe execution. The new strict production input is schema 13.

The tuple/needs-drop/signature integration passed a further full native and
ImportMIR build (1,205 jobs). Fresh material and destructor guests matched
same-TyCtxt Miri exit-zero with Lean exit-zero/cursors 348 and 418. The destructor
control checks four observable destructor effects plus ManuallyDrop, MaybeUninit
and zero-length suppression. Its `mem::needs_drop` values can fold at compile
time and are not counted as runtime query-hook evidence. Independent fresh
query comparisons passed 417 needs-drop answers (13 true/404 false, no residual
answers in that fixture), with all 188 candidate type rows omitting the covered
eager field; missing raw material and invalid destructor IDs were rejected.
Eight tuple layouts matched complete rustc layouts in ordinary and three
randomized-layout configurations. Signature planning validated 72 fresh ABI rows
(14 seeded/58 residual), ten malformed requests and two explicit residual-domain
controls. A material-only decoder fixture retains exact raw widths without
inventing a default target; recipes require actual target data. Five updated
input/constant harnesses and the primitive-range/metadata-pool regressions pass.

Generic substitution/template codecs, general univariant/shuffle, union layout,
structural Sized and pointer-metadata algorithms also have independent component
implementations/tests. Some remain unconnected to production queries; their
presence does not eliminate the corresponding residual catalogs. Full trait
selection, alias/projection normalization and generic MIR construction are being
implemented separately and are not yet available as complete runtime providers.

Raw canonical declaration templates now enter the production definition table
with typed physical definition/binder identities; the nested streaming decoder
is exercised against all 305 templates in a real fresh control export. Source
primitive/tuple/ADT field substitution has 30 pinned-rustc comparisons, but
instantiated-tree-to-runtime conversion still rejects unsupported constructor
families. This is not full generic runtime normalization.
Pointer-metadata types and Sized answers now derive from normalized structural
tails/source kinds rather than covered eager result fields; dynamic DynMetadata
construction remains residual. Union layouts use raw union type recipes and the
source-aware calculator. The repaired third integration passed native/ImportMIR
1,217 jobs and fresh ordinary, Drop and five-union-field-read guests against
same-TyCtxt Miri exit-zero. Complete union differential coverage includes eight
layouts and malformed/conflicting/missing material controls. Full Python
132 tests and semantic-source lint passed after generating audit inventories;
source-inventory review and full Lean/component regression remain unfinished.

Source MIR now has a strict material/copy-template sum: selected generic bodies
retain typed source skeletons and are instantiated on demand. Executable body
metadata scans do not instantiate MIR. The selected family covers local generic
substitution, references, arrays, tuples and control flow; unsupported calls,
drops, constants, shims and binder families remain explicit material residuals.
An independent source-MIR test constructs a nominal-element array type absent
from the exported type seeds. Component tests pass for both a small source-only
input and a full std input. A fresh 681,725-byte no_std executable also passes
same-TyCtxt Miri and the latest Lean runner finalized exit-zero. Its source MIR
creates an array absent from the material seeds. Shared source rules supply
array/pointer/reference discriminant types and non-enum facts, rather than
requiring a preexisting compiler-facts row for the new type.

Raw trait program extraction is bounded by source constructor demand. Goals
outside that declared constructor scope are Unsupported, never noSolution.
For the unchanged generic-MIR fixture and invocation, scoped material reduced
21,634,424 bytes to 111,874 bytes (95 to five traits, 7,608 to 19 impls), while
runtime type/body/template counts stayed unchanged. This measures the seed
closure repair, not final migration performance. Closed ordinary impl selection,
where-clause fulfillment and selected free/projection alias reduction execute
from declarations in Lean; specialization, universe/HRTB and other solver rules
are incomplete. Production normalization routes every nonrigid free/projection
alias through the source-rule engine and omits its eager normalized result;
unsupported providers fail explicitly without an answer-catalog fallback.
Five fresh canonical-main/current export pairs passed rebuilt Lean query checks:
ordinary generic projection, GAT substitution/own clauses, checked free alias,
checked alias with an associated-type equality clause, and an explicit unsupported
specialization boundary. The four supported controls match independent rustc
normalization, including actual `CompilerFacts` dispatch after all candidate
normalization rows are removed. Missing `Gate<u32>`, missing GAT-own `Leaf<u32>`
and a changed associated equality produce definite no-solution; the GAT-own
negative also fails pinned rustc with E0277. The genuine specialization fixture
normalizes successfully in rustc and is explicitly rejected by Lean as ambiguous;
this boundary check is not solver equivalence. Candidate sizes are 113,448,
113,211, 107,832, 112,841 and 112,079 bytes respectively. The run commands,
scoped results and source/exporter/Lean artifact hashes are recorded in
`scratch/projection-production/{results,source-manifest}.json`. These checks
exercise production query providers, not a completed guest execution or the
remaining rigid, opaque, inherent, binder and specialization families.

Canonical ADT declarations now retain source kind, lang-item identity, variant
and field-safety domains, and own clauses alongside the original generic field
templates; no computed Sized constraint is exported. Production Sized/MetaSized
trait providers inspect these expressions before runtime type lookup. Eighteen
answers over nine concrete type expressions match an independent pinned-rustc
oracle under the exact fresh compiler invocation, including six expressions
absent from the material type IDs. The cases include nested `Tail<str>`, a slice
tail, a raw-pointer field with unsized pointee, and an unsized tuple tail; three
Sized goals and all nine MetaSized goals hold. Removing canonical ADT material
produces explicit Unsupported for every ADT query, and a corrupted oracle is
rejected. The 177,871-byte input and source/exporter/Lean artifact hashes are in
`scratch/term-sized/{candidate,manifest,results}.json`. Fourteen independent
kernel component checks also pass. Binder/inference families remain explicitly
unsupported; these query comparisons are not a generic guest-execution claim.

The exporter no longer emits `discriminant_type` answers. Production derives
ordinary types as u8, coroutine state types as u32, enum discriminant types from
source representation options, and pattern/alias cases recursively. Six fresh
enum cases match an independent canonical-main rustc oracle through the actual
compiler provider after every candidate answer row is removed. This includes
`repr(C)`'s public isize discriminant type, independently of its physical tag.
All 42 type-facts rows in the 169,222-byte control omit the field (the canonical
input is 192,706 bytes). A corrupted oracle and a mislabeled primitive identity
anchor are rejected, and nine kernel recursion/error controls pass. Evidence
and source/exporter/Lean hashes are in
`scratch/discriminant-types/{candidate,manifest,results}.json`. UnsafeBinder
still requires explicit residual binder-erasure material; enum/coroutine
value enumerations remain separate residual compiler results. This is a
completed query-type port, not a general discriminant constant evaluator.

Current-artifact World component checks pass for a 64-level shared tuple DAG,
region-parameter/static erasure flags, and a genuinely new nominal-element array:
normalization, Sized, inhabitedness, needs-drop, public auto-trait queries and
discriminant types all read the same universe. Query-local fold memos prevent
repeated DAG visits and are discarded after the query. A second independent
execution deliberately reuses type number 64 for different syntax and receives
its own correct normalization result. Ten structural diagnostic type names match
an independent pinned-rustc Display oracle, including nine newly constructed
types. Raw session print limits and verbose/region flags are captured exactly;
a real limit-zero/verbose/identify-regions compiler invocation confirms those
configuration seeds. Missing print options, contextual truncation, unsupported
verbose references and a corrupt name oracle fail explicitly. Structural printing
supports scalar/pointer/reference/tuple/array/slice forms and local named ADTs
from raw DefKey namespace/symbol chains. Twelve newly constructed named/structural
types match independent rustc Display; missing raw paths fail closed. Raw session
trimming flags are captured, with active trimming, external visible paths, generic
default elision, const arguments and impl scopes still explicitly unsupported.
Local Rust-ABI FnDef diagnostics now instantiate raw signature templates and
print the exact source HIR safety/target-feature prefix and value path. Five
genuinely novel function items match ten independent diagnostic/intrinsic rustc
strings, including unsafe, target-feature, unit-return and nested-module cases.
Intrinsic type_name has a separate printer: it includes crate paths and ignores
diagnostic settings. Twelve additional novel nominal/structural intrinsic names
match rustc, including a missing-diagnostic-options control. Other ABI spellings,
nonempty binders, dynamic types and additional path families remain explicit
boundaries. The exporter type_name result enumeration, result schema and unused
result-type anchor are deleted; current native intrinsic allocation validation
is recorded separately from these string comparisons. Canonical field/variant names now enter ADT declarations as source
symbols. A second independent rustc oracle agrees on 36 Sized/needs-drop/inhabitedness
answers across twelve genuinely novel types, including generic never fields,
destructors, enum alternatives, unions, recursive references and zero-length
array suppression; a corrupted inhabitedness answer is rejected. The permanent
World component script passes; logs and artifact hashes
are in `scratch/world-types-check.log` and `scratch/world-types/`. Current World native execution passes the novel-array and tuple/Wrapper no-std
guests (approximately 701 KB inputs). The current type/instance Store wave passes
1,437 build jobs and the axiom audit covers 81,164 Miri declarations using only
the three permitted axioms. All 133 Python tests and 47 self-contained runtime
checks pass. Earlier checkpoint `d23c9e6f` stopped at covariance ThreadId-to-u64;
the bounded rigid-constructor mismatch rule now derives that false result from
source syntax, including novel types in the same World. A fresh std generic
input now passes same-prepared-TyCtxt Miri and Lean exit-zero, cursor 1430 and no
active frame. General same-constructor variance and alias/binder relations remain
residual. Artifact hashes are in `scratch/wave7-fullstd/manifest.json`.

The eager intrinsic type_name answer category and result-type anchor are removed.
Its runtime path computes the string in Lean, reserves CTFE bytes with salt zero,
checks the destination layout and adjusts a runtime allocation root before making
the slice operand; runtime IDs never enter the exported allocation-graph namespace.
A fresh three-name guest passes Miri and Lean exit-zero at cursor 437. The stable
core::any wrapper contains an anonymous const: current const_operand_json still
CTFE-evaluates it before capture. An independent pinned driver measures zero
allocations for MIR acquisition/instantiation and two at that constant evaluation.
Consequently this guest validates category removal and ordinary constant operands;
it does not establish execution of the new intrinsic adapter or a fresh-allocation
miss. Unevaluated constant seeds/Lean CTFE and raw allocator-map capture remain
necessary. See the frozen
`scratch/type-name-runtime-v2/manifest.json`.

Contextual layout operations preserve their source provenance separately from
canonical type layouts. Wide-pointer data fields and enum tag fields have distinct
operation keys even when their physical layout equals an ordinary type layout.
Seventy-two complete field contexts agree with the independent pinned compiler,
including signed wrapping tag ranges, niches, uninhabited variants, transparent
wrappers and unions. Three runtime Access regressions preserve selected-variant
u64/bool/u16 field layouts. Malformed parent, mixed recipe/eager payload and
canonical/contextual identity-conflict controls are rejected. These finite checks
do not port general enum/niche layout construction.

A default-root exporter ICE also reproduced on canonical c8daa215: a static
u32 body was incorrectly treated as a callable backtrace-frame candidate.
Callable-definition guards preserve the static body while preventing the invalid
fn ABI query. The corrected full fixture exports and its same-TyCtxt Miri run
exits zero. Long earlier Lean runs were terminated and are INCOMPLETE/NOTPASS.
The certified runtime subsequently completed the same 89,269,768-byte full
fixture: Lean finalized exit-zero, cursor 1675, no active frame, matching its
hash-bound same-TyCtxt Miri exit-zero reference. This is one finite guest pass;
no performance ratio is claimed. The latest complete library/test build passes
1,368 jobs including native runner, frontend and tests, and the axiom audit
covers 78,993 declarations using only allowed axioms; all 132 Python tests and
semantic-source lint pass. All 47 self-contained runtime checks also pass.
This does not imply that the full multi-stage regression entry point has passed.
On-demand body lowering now uses a minimal context with a kernel equality proof;
a document-local density certificate removes repeated full type-pool validation,
with kernel parity proofs. A microprobe over 8,963 types resolves exact identities
in 53–55 ms; its uncertified control exceeded ten seconds. This is a focused
algorithm diagnostic, not a full guest pass or comparative architecture benchmark.

Raw ADT declaration material now includes original kind, canonical language-item
identity, own predicates and field safety, validated against its canonical source
template. Strict FnDef material distinguishes the generic-argument binder from
the function-signature binder; three fresh rustc canonical-tree comparisons pass,
including a nonempty signature binder with an empty argument binder. Bounded
struct layouts now execute through the same source-aware resolver: ten struct
recipe type nodes and eight tuples match complete rustc layouts in ordinary and
three randomized configurations. A fresh executable checks five actual struct
field-read families against same-TyCtxt Miri and Lean exit-zero. Unsupported
parameter/alias/nominal declaration tails, SIMD/scalable and special float structs
retain explicit material layouts; new nominal type construction is not provided
by this bounded recipe.

The integrated strict input also passes a fresh 88,887,012-byte full generic std
guest: same-TyCtxt Miri and Lean exit-zero, cursor 1675, no active frame. One
CPU-pinned, single-thread diagnostic measured 6.678 s wall, 6.568 s child CPU,
564,240 KiB peak RSS, 31 same-CPU steal ticks and zero cgroup throttling/memory
event changes; binary/input/source hashes are fixed in its raw manifest. This
is not a before/after performance comparison. Checkpoint `28243a8c` passed 1,378
jobs and the axiom audit covers 79,286 declarations with allowed axioms only;
all 133 Python tests, 47 self-contained runtime checks and semantic-source lint
pass. The full multi-stage regression entry point is still unfinished. These build and
audit counts precede the current execution-owned World integration.

The same minimal generic invocation remains bounded after raw ADT integration:
111,335 bytes, 33 runtime types, 63 definitions, 38 templates, five traits,
19 impls and one MIR template/two body seeds. Ordinary source-call substitution
and effect-parametric identity resolution have actual compiler comparisons, but
covered call-containing source bodies are now selected by the producer and their
fresh same-TyCtxt Miri reference passes; current native execution is still being
validated. The existing instance/body/ABI demand graph remains residual. Sequence layouts and general
discriminant-type rules have independent components; their eager catalogs have
not yet been removed. A comparison harness freezes binaries and records
alternating CPU-pinned one-thread trials with exact child CPU/RSS and host
counters; its four identical-runner smoke checks and timeout rejection control
validate the harness only, not migration speedup.

The remaining migration includes general generic template export/substitution,
alias/projection normalization, trait selection and fulfillment (including negative,
coinductive and specialization rules), associated-item and instance resolution,
ADT/aggregate/niche layouts, target ABI adjustment, MIR generic bodies and shim
construction, constant evaluation, vtable construction/upcasting, covariance,
validity, type hashes/names, and the other compiler-owned intrinsic/platform facts.
Existing catalogs for those categories still contain rustc query results. The
exporter still closes a finite query demand graph and monomorphizes MIR. Full
migration, elimination of query closure, and rustc semantic equivalence are not
claimed. Some queries on novel arena types remain explicitly unsupported.

Historical fixtures are adapted only in test code. Where original material
cannot be recovered (old unwind answers and virtual generic counts), those
adapters use explicitly synthetic seed representatives preserving the old
component result. Such replay is not evidence that a new producer exported the
right material, nor independent ABI/rebasing correspondence. Genuine compiler
comparisons use fresh exports or focused category readers over immutable rustc
oracle data. Production readers reject schema 11/12 and eager unwind results.
The complete existing Lean harness suite and full regression entry points have
not yet passed on this migration; earlier successes elsewhere in this file do
not cover it.

## Exported input coverage

Each concrete instance and promoted index has one body seed. Covered generic
bodies reference typed source MIR templates; Lean substitutes their local types
on demand and can create previously absent pointer/reference/array identities.
Other bodies remain explicit material MIR: the exporter still substitutes,
normalizes and evaluates constants for these residual families. Raw templates
cannot execute directly; resolution validates their closed instantiated form.
Runtime storage, pointer and layout queries use the resolved types, and source
spans/scopes remain attached to resolved instructions.
The exporter aborts when requested semantic compiler data is unavailable; the
Lean input API no longer retains failed exporter payloads as execution inputs.
Successful values are serialized without success-status wrappers or a
completeness flag; consumers validate the semantic fields they use.
Compiler query catalogs and the owned final `ExportDocument` use concrete Rust
serialization types. Required vtable references finalize locally against the
closed query map;
virtual candidates are sorted and deduplicated for the exact original instance.
Pending references cannot serialize. The export document and peripheral metadata
write directly through serde without constructing a JSON Value tree. Diagnostic
fingerprints use
the emitted bytes, and prepared-reference sidecars receive the allocator frontier
directly.
Cast-query consumers, including dynamic-upcast evidence validation, read direct
result fields. Executables with custom `no_main` entry points retain startup
preflight facts and the core C-ulong and mutable i32-pointer types required by
machine construction without demanding an OS catalog. Intrinsic type-name and
caller-location constants are lowered from their direct compiler payloads. A genuine absent
function-pointer target has `resolution_kind: none` and no instance identity;
`resolution_kind: instance` carries a canonical instance ID. This preserves
the optional answer when exact query-key fields are attached.
The vtable-erasure reader uses typed predicate/type references, including
TraitVPtr child joins. Only the HRTB upcast controls require lockstep query rows;
static and cross-crate controls require direct decoding without those rows.
Resolved constants no longer retain their unevaluated definition identity, so
the cross-crate fixture checks its external constant in independently emitted
compiler MIR and checks the exported root allocation’s symbolic-vtable relocation.
This is a fixture-specific provenance check, not a general translation proof.
Local fresh wrapper checks pass for static, cross-crate, HRTB and HRTB-upcast
controls, including same-TyCtxt references, exact catalog joins over 32 salts,
and canonical Lean guest exit zero. These controls also passed the hosted
extended/fresh suites at `6a76fcbd`; the overall results and remaining failures
are described under Hosted regressions and coverage below.
Coroutine frame layout serialization and foreign TLS initializers remain
unimplemented and now stop export. This boundary does not establish compiler
query closure or interpreter correspondence.

The schema-9 follow-up emitted schema 9 and strictly supported schemas 8 and 9
at that revision (the later schema-10 baseline is described below).
Schema 8 retained its existing dense-layout and call-evidence validation and
rejects the new compact-array and LLVM no-ABI forms. Array offsets in schema 9
use an explicit stride/count formula instead of an enumerated vector. The
reader checks shape agreement, u64 bounds and the last offset without traversing
all fields; runtime lookup retains the existing checked multiplication. Local
theorems cover the exact offset value for every in-bounds index. Zero-length
and zero-stride arrays remain supported.

LLVM intrinsic calls carry explicit no-ABI evidence tied to the exact declared
FnDef type, DefId, generic arguments and current MIR call operand. Ordinary
calls still require genuine FnAbi evidence; no replacement ABI is fabricated.
Signature checks use the canonical prepared symbol registry and pinned builtin
exemptions, retaining missing, duplicate and weak-symbol behavior. The core call
implementation is unchanged.

Fifteen fixed connected inputs with their same-TyCtxt reference observations
and three eval-core inputs retain the schema-8 resolved-body typed-pool
contract. Allocation byte vectors share a document-local exact byte
image pool; function payloads group identities by Instance. Graph IDs, raw source
IDs, initialization and provenance remain independent. Prepared raw-pool slots
and indexed salt results derive serialized facts from those allocation nodes.
Span and backtrace filenames remain validated numeric IDs
in a shared exact-string file table until diagnostics or backtrace APIs present
them. Runtime-metadata checks export their
Rust inputs afresh. Performance checks now obtain
fresh producer inputs. The DST and large Tree Borrows connected cases now
generate inputs and same-TyCtxt references in CI from unchanged tracked sources,
flags and reviewed guest configuration; fixed assertions and choice tapes are
preserved. This adds pinned toolchain/sysroot build cost and replaces saved
allocation-history replay for those two cases. Their historical archives are
not CI inputs.
The 17-case Lean connected replay passes under schema 7 with unchanged expected
outcomes, including fresh same-TyCtxt references for the DST and large Tree
Borrows cases. Decoder controls reject missing byte images, repeated identities,
unmatched raw slots, incomplete salt arrays and unchecked foreign TLS
initializers. A decoded shared-byte cyclic graph retains distinct runtime IDs,
mutability, initialization and CTFE provenance flags.
The earlier hosted replay lane also passed at `6a76fcbd`. Neither result
establishes validation of the schema-9 follow-up source; the
broader hosted results and remaining failures are described below. These finite
executions do not establish compiler query closure, interpreter correspondence
or whole-machine safety.

## Empty-function caller-domain transport

The [empty-function proof](examples/empty_function/README.md) covers actual call
initialization and every finite in-call prefix under its explicit `Metadata`,
`Profile`, `RuntimeProfile` and `CurrentInputDraft` assumptions. A theorem that
every Rust-valid caller state satisfies this domain remains absent. The domain
includes raw caller, representation, pointer/source, memory/borrow, address/ID
and runtime coherence; agreed pure metadata facts remain explicit assumptions.
Compiler/exporter correctness and Rust/interpreter correspondence remain trusted.

The target admits checked non-UB stops, including resource exhaustion; it does
not claim normal return or NoErrors for every resource supply. Allocator
coherence is guarded by active raw runtime and enabled-source counters, rather
than excluding zero/wrapped counters, exhaustion flags or the final MAX ID.
The exact race-off/shallow/fixed-scheduling profile is in `Specification`;
other scheduler interleavings and caller execution after return are outside scope.

The example adapter disables the new allocation-backtrace diagnostic option
through `Configuration.proofOptions`, preserving every pre-existing option.
The proof covers this legacy diagnostic-off profile; collection-enabled UI
executions are separate finite comparisons. Fixed Rust/MIR inputs and the
target theorem are unchanged.

## Remaining general proofs (not acceptance conditions for current finite QA)

### Forward simulation from real steps to atomic events

The relation from [EvalCoreMachine](Miri/Input/EvalCoreMachine.lean),
[execution configuration](Miri/Input/EvalConfigurationCore.lean) and
[AtomicDispatch](Miri/Concurrency/AtomicDispatch.lean) to the
[local SC projection](tests/connected/proofs/ScProjection202.lean) remains unproved.
Next, define observations for the 4 X/Y events in real connected states and prove
that every permitted step stutters or extends the observations while preserving
static identity and each worker's store-before-load order. Re-enumerating the
6 local orderings does not resolve this. Resolution requires a kernel-checked
inclusion theorem for actual connected steps; reverse reachability of every
abstract ordering is not required.

### HB connection for join/reporting and correspondence with real memory

[JoinReadProof195](MiriTests/Connected/Proofs/JoinReadProof195.lean) is a local theorem
with HB assumptions. Worker reporting stores, termination clocks, successful
joins and main's result loads must be connected to
[Thread](Miri/Concurrency/Thread.lean),
[WeakMemory](Miri/Concurrency/WeakMemory.lean) and the real memory path.
Next, establish correspondence for HB assumptions, buffer/range identity and
initialized physical fallback reads, including intervening steps. Resolution
requires deriving the local theorem's assumptions from real connected states.

### Lift strict-choice normalization to the whole machine

[History erasure](MiriTests/Connected/Proofs/ChoicePublic217.lean),
[current-input locality](MiriTests/Connected/Proofs/ChoiceLocality220.lean) and
[demand](MiriTests/Connected/Proofs/DemandProof211.lean) are component theorems for
strict wrappers. Next, define a relation retaining fresh events and the unread
input suffix externally, and prove preservation by real machine steps.
Resolution requires a quotient theorem over the full machine relation.
It does not apply directly to seeded/bounded diagnostic policies, which require
separate assumptions and proofs.

### Exclude UB on every permitted finite prefix

No-(0,0) at normal termination alone does not exclude UB partway through a prefix.
The properties in [OperationalSafety](Miri/OperationalSafety.lean) still need
to be instantiated for the real connected machine and target inputs/contracts.
Next, use the connection lemmas above, handle all other nondeterministic choice
families or state fixed assumptions explicitly, and exclude reachable UB.
Unsupported, interpreter errors and fuel exhaustion must not become successes.
Resolution requires a kernel-checked theorem specifying the target, initial
conditions, external contracts and permitted choices.

The [connected graph explorer](tests/connected/proofs/ConnectedGraph215Schema3.lean)
and [exact state comparison](MiriTests/Connected/Proofs/ExactStateCodec207.lean) are
reusable, but exploration has no complete capture or established completion bound.
`bash tools/check-connected-proofs.sh` only typechecks these. Increasing the
budget of OPEN exploration does not resolve the proofs above.

## Validation gaps within scope

### Hosted regressions and coverage

At merged main `6a76fcbd2f24afaf6c0114efc205479560fb280b`, the
[Miri regression run](https://github.com/proofs-rs/lean-miri/actions/runs/43069997521)
passed the regression, fresh and replay lanes. Extended passed 21 of 22 suites;
its sole failure was the detached-join source-order check's stale whole-file
`ThreadMachine.lean` SHA after allocation initialization changed. The checked
`joinExclusive` slice is byte-identical to the prior reviewed implementation.
The local SHA refresh passes the unchanged ordering assertions; a hosted rerun
of that refresh and subsequent changes remains required.
See [CI coverage](tools/ci/README.md) for lane commands and artifacts.

Upstream main subsequently advanced through the allocation-compaction and wire
field-deduplication revisions to schema 8 at
`affc8c4128cda426557eeb5c04d273d1602917b5`. Its latest hosted runs are
[Miri regression](https://github.com/proofs-rs/lean-miri/actions/runs/43085783786),
[UI](https://github.com/proofs-rs/lean-miri/actions/runs/43085783770),
[empty-function proof](https://github.com/proofs-rs/lean-miri/actions/runs/43085783789)
and [documentation](https://github.com/proofs-rs/lean-miri/actions/runs/43085783868).
At that upstream revision, documentation build/deploy and the empty-function
proof passed, as did the fresh regression lane. Replay failed only at the stale
SC-snapshot SHA; its build, reference-profile, canonical12, ordering and large-TB
suites passed. Extended failed only at the stale detached-join file SHA. Both
pins are corrected in this follow-up, with their original checks retained.
The regression lane also failed: its constant-parser reference test added a
legacy single-identity function allocation, which schema 8 correctly rejected
before the intended dangling-instance mutation. The local fixture now uses the
schema-8 identity group and a fresh graph/source identity; the full constant
suite passes while still rejecting the legacy form and dangling instance IDs.
UI shards were still queued when checked. These upstream results do not validate
the integrated local follow-up; its completed local checks are recorded below
and a new hosted result is required.

At `6a76fcbd`, the successful hosted suites include timezone with Cargo-reported
libc archive selection, fresh producer/decoder u128 boundaries, powi and all four vtable
controls, supplemental guests, native/TLS query-demand mutations and runtime-type
closure. The replay lane includes canonical12, ordering, large-TB and SC schedules.
Pinned reference Miri and MIR-enabled standard-library setup also completed.
These results validate that revision's scheduled checks, not later producer or
interpreter changes. Fresh regeneration/comparison of every canonical guest and
standalone unregistered harnesses remain outside workflow coverage; saved replay
cannot validate changed producers.

The upstream UI workflow applies the requested reference and Lean settings
through explicit opt-in adapters: empty guest environment, seed zero, source
argv0, one CPU, and ordered supported runtime flags. Ordinary runner defaults
are unchanged. The uncapped seeded diagnostic policy uses SplitMix64; it does
not claim the same random stream as Miri. Strict profile and terminal oracles
retain per-field expected, observed and missing values.
The optional allocation-time collector retains full-instance/span frame traces
for allocations subject to leak checking, including MIR inline scopes and exact dummy
span fallback. UI profiles enable it unless leaks are explicitly ignored;
ordinary runner defaults keep it disabled. Eight focused unchanged upstream
sources pass the strict reference/profile/terminal oracles, including an actual
UB stop with fourteen retained allocation backtraces. Native leak-report
rendering remains Unsupported and needs implementation. This does not establish
the full UI sweep: coroutine coverage was still unsupported in that cohort; see
the schema-12 follow-up below. Remaining gaps include Stacked
Borrows profiles, host-isolation/output-capture settings and compile-time or
nonlocal-diagnostic oracles outside the runtime profile. Export errors,
Unsupported outcomes and other interpreter mismatches remain failures.
The [merged-main UI run](https://github.com/proofs-rs/lean-miri/actions/runs/43069997560)
completed all 32 comparison shards, each failing. Their terminal console summaries
cover 1,118 revision/profile cases: 600 passed, 309 profile-unsupported, 119 UB-kind
mismatches, 47 export failures, 22 Lean Unsupported outcomes, eight UB-site
mismatches, five timeouts, four Lean failures, three failed Lean processes and
one reference-annotation mismatch. No profile mismatch was reported. The
inventory-coverage collector subsequently confirmed `complete=true`,
`passed=false` and `expected_cases=observed_cases=1118`, with exactly these
counts. This establishes inventory coverage, not a successful UI sweep.

The earlier `6aca6f0` failures in SC schedule validation, powi root lookup,
vtable wrappers and JSON-natural u128 endpoints are covered by the successful
`6a76fcbd` hosted suites above. Local follow-up checks do not establish a new
hosted result. All local stages of `tools/check.sh` have now been exercised as
described below; a successful hosted follow-up matrix remains outstanding.
Selected finite checks do not close general proof or source-correspondence gaps.

The following local results belong to the schema-8 baseline merged in PR #44
as `54749934`. Its new hosted checks were queued when last checked; the full
hosted result for that revision is still pending.

Local baseline checks pass the concrete runtime Codegen ABI probe and 20
exporter boundary tests, including nested bound-region query views and the exact
callee ABI needed before rejecting a variadic fixed-count mismatch. Five
unchanged variadic guests, four focused diagnostic guests and four UB-kind
controls pass their strict local reference/profile/terminal oracles. This does
not provide a new hosted result. Coroutine runtime ABI queries succeed in the
probe; coroutine coverage at that revision remained unsupported; see the
schema-12 follow-up below.

The shared compiler-owned `miri_start` selector passes two focused no-main
guests, but `pass/no_core.rs` still fails with `compiler named types absent`
after its matching reference exits zero. The dedicated unsized uninitialization
writer passes exact dynamic-range, permission-partial-state and zero-size checks.
After explicit tuple cast classification, the unchanged `pass/unsized.rs@tree`
guest passes a fresh same-TyCtxt reference and Lean execution with exit zero and
matching strict profiles. This is a finite local result, not a new hosted sweep.

The frozen schema-8 follow-up passes the 1,281-job library/test/native build,
46 self-contained runtime checks, the quick check with 110 Python tests, 36 Rust
unit tests, the direct runtime-ABI integration probe and the 20 producer boundary
checks. The library axiom audit covers 74,171 declarations with only `propext`,
`Quot.sound` and `Classical.choice`. SC seeds 0–11 and four malformed-log controls,
and 16 selected genuine UI cases, pass their unchanged local assertions/oracles.

For that baseline, all 66 `tools/check.sh` stages pass across resumed local runs:
stages 1–57 passed first, stage 58 passed after updating its tuple-classification test
expectation, and stages 59–66 passed after five input harnesses installed the
actual supplied allocation world through the canonical initialization path.
These were test-only corrections; Miri sources, proof sources and fixed inputs
remained unchanged. The reference exporter was restored to its recorded frozen
binary hash after the default-exporter checks.

All 268 empty-function proof roots pass on that baseline source. Its transitive
axiom audit covers 76,837 declarations using only the same three allowed axioms;
recorded Rust, input, library and proof hashes match before and after validation.
These are completed local results, not a successful full hosted matrix or a
whole-machine correspondence theorem. Hosted validation of the integrated
follow-up is still required. The no-core, full-UI and performance gaps remain
unresolved.

A separate diagnostic follow-up on `54749934` retains the reborrow cause at
the actual parent-access failure in both retag paths. A kernel-checked equality
preserves the default protector-release classification and message. The UI
oracle recognizes the exact existing `InvalidTag(outside valid range)` and
`dereferencing a null box` diagnostics; unrelated UB, access directions,
Unsupported outcomes and missing source sites remain rejected.

This follow-up passes the 1,281-job common build, 46 runtime checks, structural
regressions and the quick check with 111 Python tests. Six unchanged upstream
guests pass strict reference/profile/UB-category/site checks, covering TB
read/write/reborrow, destructor protection, enum tags and null boxes. Its library
axiom audit covers 74,172 declarations; all 268 empty-function roots and their
76,838-declaration transitive audit pass using only the same three permitted
axioms. Recorded Rust, input, library and proof hashes match before and after
validation. The 66-stage result remains specific to the baseline; this diagnostic
revision still needs full hosted validation.

At subsequent merged schema-8 main `7cc6b6cc`, the hosted empty-function proof,
documentation build/deploy and all four core lanes (fresh, replay, extended
and regression) pass. The UI sweep remains unfinished; its shard-9 AVX2
export failure used the old producer and is covered by the local repair below. These results
belong to that main revision; schema 9 has not yet received hosted validation.

### Standard-stream effects: local validation

With an inherited private control descriptor, the native runner connects actual
stdout/stderr writes to a checked typed transcript. A missing observation stops
the pure attempt; the outer IO controller performs one real host operation, then
restarts a fresh machine with identical supplied choices, seed and policy.
Recorded observations are checked and replayed without repeating host IO.
The first pending request survives cleanup error replacement; missing state,
changed journals, malformed responses and unconsumed suffixes fail closed.
Without the control descriptor, previous Unsupported callbacks remain in place;
the new World slot defaults to `none`. Its disabled callback is definitionally
the previous callback. Arbitrary host files are not enabled, and source muted
ordinary stdout/stderr descriptors remain NullOutput.

The pinned Rust backend calls `Write::write` once and retains its count/error;
source write_all owns short-write/Interrupted handling. Source flushes and outer
host finalization are distinct. All boundary/profile/terminal records use the
private control channel, so guest output cannot supply an acceptance record.
Finite fresh reference/Lean checks passed for repeated and binary explicit
output, spoofed protocol lines and preserved NullOutput, plus all four original
cell-inside-box/struct tree/tree_implicit_writes cases with workflow budgets and
original sources/flags/profiles. The final scoped-link cohort used immutable
exporter `38f5811b…3203` and native runner `e5643e70…cb7b`.

Local validation passed the common build (1,299 targets), audit of 74,890 Miri
declarations, all 47 existing runtime checks, quick checks including 128 Python
tests, structural checks including pure replay/protocol and compiled native QA,
and three Rust boundary tests. The fixed SC suite passed all twelve seeds and
four negative controls. All 268 fixed-input proof modules passed; the transitive
audit covered 77,532 imported EmptyFunction/Miri declarations with only the
three permitted axioms. Fixed Rust/input hashes and frozen proof/library source
bindings passed. The later Lake-only link isolation leaves those Miri/proof/input
bytes unchanged; final native QA, runtime, structural and genuine comparisons
were repeated after relinking.

The native archive is a dedicated runner-support target rather than a global
package external library. An isolated client executable and `Miri:shared` built
without a Rust toolchain, with zero Rust/Cargo sentinel calls and no stdio
archive generated; runner/QA targets still failed explicitly without Rust.
Hosted validation remains pending. An unwound attempt is never resumed.
Raw host errno is retained; unavailable host errno conversion remains
Unsupported. No general stdio error support, crash recovery guarantee or
whole-machine proof follows from these finite checks.

### Source-owned descriptor cleanup: local validation

The follow-up on main `4fd7d0fe` connects virtual sockets, eventfd and epoll
last-owner destruction to their canonical ownership/protocol/readiness stores.
Narrow drop dictionaries reuse the pinned bodies without provisional I/O
capabilities. Virtual close retains peer-loss notification and the owned delayed
readiness reference before watched-field cleanup; eventfd removes its watched
metadata before its state; epoll releases its watcher reference. Both release
routes retain the actual payload and reject tag/identity mismatches. Legacy
callback defaults, partial failure state and true host-resource limits remain.

The native fixture also constructs the pinned simple ErrorKind representation
(kind unchanged, raw errno absent, Unit payload). Existing ordered target tables
still obtain numeric errno from compiler constants. Raw host conversion, host
errno lookup and error display remain unavailable; unmapped kinds or missing
target evidence do not become successful errno conversions.

The coherent 1,285-job combined build, final runner incremental build and
74,519-declaration library axiom audit pass with only the three allowed axioms.
The latest quick check passes all 119 Python tests. All 46 runtime checks and structural
regressions pass, including the new descriptor and simple-kind controls. The
unchanged `pass/shims/socket-unix.rs` passes a fresh same-TyCtxt reference/Lean
comparison using rustc's default crate name, strict profiles, source/snapshot
bindings and frozen binaries. The earlier cleanup-only run reached EOF handling but stopped at the then
missing WouldBlock conversion; it is not counted as a successful execution.

The fixed Rust/MIR inputs, checksums, proof targets and caller assumptions are
unchanged. All 268 frozen proof roots pass; their transitive audit covers 77,185
declarations with only the same three allowed axioms. Library/proof/input hashes
match before and after. The final driver-only rebase retains identical library,
runner and exporter sources. These finite local results do not establish a green hosted UI sweep,
host socket support or closure of the other capability/performance gaps.

### Schema-11 shared-layout test corrections

On main `62129c87`, the test-only follow-up resolves logical layout IDs through
`layouts` into `layout_values` before mutating the exact scalar/niche payload.
Decoder mutation helpers parse JSON natural values instead of calling a JSON
accessor on raw strings. The MIR fixture validator checks schema-11 locals'
exact three fields and resolves their physical layout through the type graph,
rather than requiring the removed redundant local layout field.

All 26 producer boundary tests, nine Rust integration suites and the complete
`tests/input/run.sh` pass locally. Primitive compiler/runtime ranges remain
exact: all six decimal/numeric endpoint cases pass, and all eleven malformed or
overflowing inputs remain rejected for both scalar and niche endpoints. The
schema-10 input suite also passed before rebasing. Interpreter/decoder source,
fixed Rust/MIR inputs, checksums and proof assumptions are unchanged; no release
exporter feature toggle was needed. These results repair test compatibility,
not interpreter semantics, and do not establish a new hosted result or close
the remaining gaps.

### Schema-10 UI oracle follow-up: local validation

The oracle-only follow-up on main `17330f08` changes two test/harness files.
Vtable-specific reference diagnostics take precedence over generic null-pointer
wording while uninitialized-value precedence remains intact. The calling-
convention category accepts the exact shim-convention diagnostic. The no-
provenance category recognizes only the fully qualified, case-exact typed
`Miri.Memory.AccessError.danglingIntegerPointer` constructor with a nonzero
canonical decimal address and strict namespace/integer-token boundaries.
Adjacent ABI errors, zero addresses, other namespaces, malformed address tokens,
bounds/dead-allocation/vtable errors and generic UB remain negative controls;
wrong sites and Unsupported outcomes still fail.

The latest-base quick check passes all 114 Python tests, including 19 UI-oracle
unit tests. Fresh strict comparisons pass the four repaired cases
(`invalid_wide_raw`, `check_arg_abi`, `deref-invalid-ptr` and `cast_dangling_ref`)
and two existing null-box/null-reference controls. These comparisons use sealed
schema-10 binaries from the separate Unix-allocation candidate `11c7e251`, also
based on `17330f08`: exporter SHA256 `1e0b4eb44eeddb9aa6ebdab13932c5166d773244b7f478a519e1f31471ec443a`
and native runner SHA256 `d2a20a77451114ed9881cde05d0423f7091631e3130eddeb07261fa0b0c96d9a`.
That candidate adds configured Unix allocation ownership; its vtable, foreign
ABI and memory-access cause sources have exactly the same SHA256 as this
checkout, with no terminal diagnostic changes. Source/binary identities,
same-TyCtxt snapshot bindings, strict profiles and exact source-line checks all
pass. This is a combined-candidate comparison, not a pure-main binary result.

This follow-up changes no Miri/proof source, protocol, line matching, profile,
budget or case inventory. The 268 proof roots were not rerun for these oracle
changes. The adapters identify the actual source UB causes; they do not turn
unrelated failures into accepted UB or close the remaining implementation gaps.
On hosted main `17330f08`, the proof, fresh lane and documentation build pass;
other checks are still in progress when checked. These local six-case results
do not establish a green hosted UI sweep.

### Unix allocation ownership follow-up: local validation

The follow-up on schema-11 main `62129c87` uses the existing configured
allocation helpers for Unix allocation, ordinary reallocation and Linux
`mremap`. The canonical configuration already owns extras initialization;
wrapping it again caused the first aligned allocation in the unchanged upstream
`heap_allocator.rs` guest to fail with `allocation extras initialized twice`.
The duplicate-ID guard remains strict. Allocation identity, initialization,
provenance-aware copying and late deallocation retain their existing ordering
and failure effects; ordinary reallocation keeps uninitialized growth while
`mremap` keeps zeroed growth.

The 1,283-target common build, 46 runtime checks and structural regressions pass
on this base. The library audit checks 74,397 declarations using only `propext`,
`Quot.sound` and `Classical.choice`. Component assertions cover aligned
Zero/Uninit allocation, fresh identities, duplicate initialization rejection,
pointer-provenance and initialization-mask copying, both growth policies, and
retained state after copy/free failures. A fresh Linux control passes strict
same-TyCtxt Miri/native comparisons through C allocation/reallocation/free and
mmap/mremap/munmap, including copied bytes, page alignment and zeroed growth.
Source, snapshot, profiles and frozen executable identities match. All 268 proof
roots pass on schema 11, with a transitive audit of 77,063 declarations using
only the same three allowed axioms. Fixed Rust/input checksums and library/proof
bindings match before and after. After rebasing onto main `3241cb6b`, all 1,012
recorded library, runner, test, proof and fixed-input source hashes remain
identical, so this proof result also applies to those unchanged sources.
The exporter rebuilt from that latest base also passes the fresh strict
three-route control with the hash-matched schema-11 native runner.

The preceding schema-10 cohort passed all 268 roots and its 77,078-declaration
transitive audit with only the three allowed axioms. Its original unchanged
`heap_allocator.rs` guest nevertheless timed out at the CI-default 900 seconds:
the reference exited zero and both profiles matched, but Lean produced no
terminal outcome. Schema 11 trims input representation without changing the
post-start interpreter, so this long probe was not repeated without evidence
of a relevant execution improvement. Original-case completion and full hosted
UI validation remain unresolved. The older 600-second timeout and deliberately
stopped 1,800-second probe remain separate schema-9 observations.

### Unsigned x86 pack saturation: local validation

The hosted AVX512 input reached an interpreter failure for the valid unsigned
value 255. `IntrinsicX86.pack` clamped unsigned results correctly but constructed
them through the signed `Scalar.fromInt` path, rejecting an 8-bit result above
127 (and analogously a 16-bit result above 32767). The unsigned branch now uses
checked `Scalar.fromUInt`, matching pinned `packuswb`/`packusdw`. Signed
construction, input reads, saturation bounds, chunk/lane order, layout and ISA
checks are unchanged.

Fresh reference/guest comparisons pass the minimal 255 case, a signed 127
control, and twelve explicit signed/unsigned vectors through the real
128/256/512-bit dispatchers. These cover negative-to-zero unsigned saturation,
upper bounds and out-of-range inputs, signed extrema, and distinct 128-bit chunk
markers. The 128-bit i32 fixture covers the low side; u16 upper boundaries are
covered at 256/512 bits. The original unchanged
`pass/shims/x86/intrinsics-x86-avx512.rs` also passes its strict official driver
with the original CPU flags/profile and CI-default 600-second budgets. Source,
prepared-reference FNV/length, profiles and executable identities match.

On the combined Unix-allocation base `bbee5d19`, the 1,283-target common build,
46 runtime checks and structural regressions pass. The library audit checks
74,397 declarations; all 268 fixed empty-function roots pass with a transitive
audit of 77,063 declarations. Both audits permit only `propext`, `Quot.sound`
and `Classical.choice`. Fixed inputs, proof claims and caller assumptions are
unchanged. An earlier pre-Unix proof run was stopped after 224 module starts;
it is incomplete and is not included in these results.

After the exporter-only rebase onto `c390bf41`, every recorded library source,
all 268 frozen proof sources and the fixed-input manifest remain identical.
The refreshed reference-enabled producer (SHA256
`0325af2577967180f1aae3ee76483aca265d7c2fae90ae5ba8e533c1bc0f8811`)
and hash-matched native runner (SHA256
`45acc1b882004f65fa4492032e279df026b8c4fea2711383a74a39d32efebd08`)
pass all three fresh pack fixtures and the original AVX512 file again. This also
exercises the assertion harness's reference arguments after the covariance
metadata update. Hosted validation of this pack follow-up remains pending.
These finite comparisons do not establish general x86 equivalence or all-prefix
safety for other guests.

### Schema-9 metadata follow-up: local validation

On the follow-up rebased onto `7cc6b6cc`, the full 1,281-job library/test/native
build, 46 runtime checks, structural regressions and decoder controls pass.
The library audit covers 74,294 declarations using only `propext`, `Quot.sound`
and `Classical.choice`. SC seeds 0–11 and four malformed-log controls pass with
their source/artifact seals. All 268 empty-function roots also pass; their
transitive audit covers 76,960 declarations with only the same allowed axioms.
Fixed Rust/MIR input bytes, SHA records, final target and caller assumptions are
unchanged, and the recorded library/proof bindings match before and after.

All 66 `tools/check.sh` stages are covered across resumed local attempts:
stages 1–50 passed before stage 51 encountered a missing vanilla-reference build
manifest in the isolated checkout. Reuse of the existing pinned vanilla Miri
build was verified against its compiler/Miri pins and binary SHA256, then stages
51–66 passed. This is neither a single uninterrupted run nor a fresh reference
toolchain setup. The reference-enabled exporter was restored to its recorded
pre-run binary SHA256 after the suite's feature toggles. After the final
Rust-only LLVM helper correction and affected checks, the reference exporter
was restored to SHA256 `5073ff656c24aa107678d4dbf8750f465d14b2978406b8669335706c20ec9c37`.
Miri sources and the fixed library/proof bindings remain unchanged.

The Rust checks pass 37 unit tests, the independent runtime-ABI integration probe,
24 producer boundary tests and nine reader checks; nine affected Rust suites
also pass. Eight focused LLVM controls cover three successful executions and
five negative outcomes with strict reference/profile/terminal checks. Unknown
Unsupported and invalid-layout rejection are not counted as guest safety
passes. Malformed identity, type, operand and ABI evidence retain rejection.
Two ordinary function-pointer/exported-symbol comparison cases and the affected
input, frontend, runtime-metadata and execution checks pass. A second route
through the ABI-synthesizing helper is now excluded only for LLVM intrinsics;
ordinary Rust helpers retain their ABI requirements and genuine query failures
remain fail-closed. The former 1-PiB offset-vector abort in the
unchanged upstream `pass/align_offset_symbolic.rs` is locally repaired: a fresh
schema-9 export completes both same-TyCtxt Miri and Lean execution with exit zero
and matching symbolic-alignment profiles, including a final fresh comparison
with exporter `5073ff65` and native runner `09ccb6b0`. A separate guest retains 1-PiB byte
and word array layouts plus `usize::MAX` zero-sized elements without allocating
those arrays; its approximately 1-MB export and both executions pass with exact
snapshot bindings under the earlier `6043755a` producer; its array implementation
is unchanged by the final LLVM-only Rust correction. Compact/dense layout boundaries, overflow and version
rejection controls pass while the fixed schema-8 example input remains intact.

These are finite local results, not a green hosted UI sweep, general query
closure proof or performance claim. All four original export-failure probes
(`intrinsic_target_feature`, SSE2, AVX2 and AES/VAES) now export successfully.
The unchanged target-feature case also passes its official strict comparison;
execution of the three long SIMD files has not been measured. Export success
does not establish their execution result. The no-core, coroutine-layout, native leak-report
rendering and performance gaps above remain unresolved.

The ordinary standard-library startup closure from
`tests/repro/startup/empty-main.rs` now decodes directly into MIR. A fresh
7,322-body export completed native execution with `finalized_exit code=0` under
the bounded-diagnostic-zero choice profile. This finite witness does not establish
behavior for other standard-library closures or all permitted choices.

### Compiler query closure and prepared allocation identity

General query closure remains unproved for the [exporter](exporter/src/main.rs),
[allocator world](exporter/src/allocator_world.rs),
[CompilerAllocIdWorld](Miri/Input/CompilerAllocIdWorld.lean) and
[Decoder](Miri/Input/Decoder.lean). Retain genuine fresh exports exposing
uncollected queries and extend producer closure from their typed keys and source
operations. A target reproduction must pass fresh export → real connected
execution while missing keys still produce Unsupported. This does not require
query completeness for every program or agreement with vanilla Miri's raw
AllocId history. Entry function pointers, backtrace frame Instances, Offset
overflow pairs and memory-backed vtable providers already have implementations
and finite controls; investigate actual missing queries before extending them.

Nonidentity erase/anonymize vtable queries still lack genuine producer-to-consumer
validation. Pin a triggering input and check the join between
[VTable](Miri/Interpreter/VTable.lean) and the compiler catalog, distinguishing
all 32 salts, type/predicate identity and raw/dense IDs. A dynamic vtable's CTFE
salt0 probe is not its runtime-salt ID. Use [erasure controls](tests/repro/README.md)
and `tools/check-vtable-erasure.py --trace-queries`: a changed catalog pair must
actually be consumed by the connected runtime, alongside fresh reference,
query/catalog and salt checks. Catalog rows from roots/templates or TraitVPtr
children do not establish runtime consumption. Identity controls and synthetic
changed pairs cannot discharge this branch.

Before adding syntax variants, investigate whether noncanonical pairs are
reachable. Pinned rustc normalizes/erases successful MIR queries, CTFE vtable
creation and TraitVPtr principals; its normalization provider also erases the
resolved result after alias normalization. Struct-tail traversal normalizes
fields without unconditionally rewriting its initial input pair. Metadata
decoding preserves the encoded pair, and `reserve_and_set_vtable_alloc` itself
does not normalize. HRTB, upcast, static and cross-crate metadata controls have
retained identity pairs only. These controls and source tracing do not prove
canonicality preservation across type extraction, metadata decoding and recursive
demand closure, or general nonreachability of nonidentity pairs. The TraitVPtr
provider lies outside the selected local rustc source corpus.

The exact generated-call ABI collector is locally validated on the schema-11
`054990d8` baseline. It preserves source helper-signature keys before region
normalization and includes demanded weak foreign-static symbols in named-shim
queries and catalog invalidation. Rust units (46), the runtime-ABI probe,
producer checks (29) and integration suites (9, including Python discovery)
pass. Three minimal Result-main/getrandom/GNU TLS guests pass strict genuine
comparisons; deleting the required queries or mismatching the startup argument
type leaves four explicit Unsupported reader outcomes. The consumer is a
separate schema-11 candidate containing Unix allocation-adapter changes, with
matching ABI/protocol/main source modules; this is not a pure-main binary claim.
Unchanged upstream `main_result`, `static_align` and `const-addrs` also pass.
`float_extra_rounding_error@random` reached the unchanged 180-second local native
wall limit after reference exit zero and is not counted safe. No-std weak-symbol
probes can still fail on the eager OS catalog's missing `libc::pid_t` prerequisite;
the successful weak-symbol controls use std. These finite checks do not establish
a closed compiler-query domain or a new hosted sweep. This collector patch changes
no Miri source, fixed example input, library binding or execution budget.

Shared `CoerceShared` reborrows now add their exact source-place/target-type
pair to the existing rustc covariance query collector, only on the shared
`copy_op_allow_transmute` path. The compiler's FALSE answer for distinct
same-layout ADTs is preserved; unknown evidence is not defaulted to FALSE.
On the schema-11 `bbee5d19` baseline, 46 Rust units, the runtime-ABI probe,
30 producer checks and nine integration suites pass. The unchanged upstream
`reborrow-coerce-shared` passes its strict reference/Lean comparison, while
missing, mismatched and conflicting query controls remain Unsupported.
Primitive identity still yields TRUE and an unknown distinct pair remains an
error. Miri sources, fixed inputs, proof assumptions and budgets are unchanged;
these finite checks do not establish general covariance-query closure.

The UI oracle now recognizes the complete shim argument-ABI diagnostic only
as an argument-type failure, separately from convention, return and count
errors. Niched-variant writes have their own category and exact constructor,
so an invalid-discriminant read cannot substitute. On main `c390bf41`, all
117 quick Python checks and 20 UI units pass. The two original failing cases
pass strict comparisons; the final tightened predicates also pass on those
unchanged source/snapshot/sidecar/binary-bound records. No Rust/Lean semantics,
fixed inputs, profiles, crate naming or budgets changed. Bare dangling-pointer
null classification remains a separate unrepaired diagnostic issue; the
extern-static crate-name mismatch is addressed below. This does not establish
a hosted sweep.

The UI driver no longer injects a fixed crate name. The compiler therefore
owns filename normalization, source `crate_name` attributes and explicit case
flags, with the same compiler configuration for the export and prepared
reference. Driver fingerprints reject results from the previous configuration;
source, sidecar, byte/FNV, site and profile checks remain strict. The oracle
separately recognizes the complete extern-static backing-size-or-alignment
failure, without accepting generic alignment, mutability or non-UB failures.
On main `d3d79e8e`, 119 quick Python checks (including 21 UI units and nine
collection units) pass. Both unchanged wrong-size cases and three typed
`type_name` controls (hyphen filename, attribute and distinct explicit flag)
pass fresh strict comparisons and actual compiler-name checks. Representative
generated-ABI checks (three genuine and four malformed-query controls),
reborrow checks (one genuine and three malformed-query controls), and the five
LLVM controls pass with the new driver. These are finite local comparisons;
Miri/exporter semantics, fixed inputs, proof assumptions and budgets are unchanged.

Function-pointer allocation failures now retain the actual integer address,
size zero and dereferenceable-pointer context through the existing typed
memory-error converter, matching pinned `ptr_get_alloc_id`. Both missing
provenance and failed exposed-address lookup retain the original UB branch,
resolution order and partial state. Seven kernel-checked component lemmas cover
arbitrary addresses/provenance and whole-state equality for failed/successful
lookups, propagated errors and function-pointer success/offset/nonfunction
classification. Null, nonzero and successful backtrace capture/resolve controls
pass fresh strict comparisons; bare `DanglingIntPointer` is not a null alias.
The common build, 74,541-declaration axiom audit, 119 Python checks and structural
regressions and all 47 runtime checks pass. The fresh 268-module empty-function
proof closure also passes, including source/input binding and the transitive
allowed-axiom audit for its existing explicit input/profile domain.
Three older backtrace API/invalid-flags UI cases remain excluded by the existing
stdout-snapshot/expected-Unsupported profile guards and are not successful
comparisons. Fixed inputs, proof assumptions and execution budgets are unchanged.

### Schema-12 coroutine metadata follow-up

The producer now captures compiler-owned coroutine layout/source metadata and
role-qualified auxiliary drop bodies. The strict reader retains this evidence,
validates state/field/projection identities and full physical variant layouts,
and keeps auxiliary snapshots outside callable body identities. Canonical drop
shims still use compiler `instance_mir`; no resume/yield execution mechanism or
profile exclusion was added. Schema 11 remains accepted byte for byte and
forbids the new table; schema 12 requires complete explicit body markers.
Native-callback FnSig collection distinguishes normal closures from coroutine
instance types, without substituting runtime FnAbi for a missing signature.
Resolved runtime constants use the actual Miri Codegen environment; raw auxiliary
snapshots retain their compiler context and phase. Generic or unavailable facts
still fail closed.

On merged-stdio main `4287d180`, the common build and 75,361-declaration axiom
audit pass, as do 47 runtime checks, structural regressions, SC seeds 0–11 and
four malformed-log controls. Fresh strict comparisons pass the four original
future/generator profiles and two suspend/drop/completion controls; the stdio
binary-output/control-isolation comparison also passes with the new schema pair.
Provider checks preserve exact coroutine runtime ABIs while rejecting missing
native callback signatures, and three mutations fail with their expected
coroutine witness/source-definition/physical-layout decoder diagnostics. An
initial QA wrapper compared a process object with an integer after six successful
comparisons; only the wrapper/provider/mutation portion was corrected and resumed
on unchanged source/snapshot/binary-bound records, not counted as six new runs.
Exporter Rust units (44), Python checks (45) and the combined quick check (128)
pass. The complete input suite and all 20 maintained schema-11 inputs also pass
(15 connected, three eval-core, fixed empty-function and strict unit); two older
schema-3 archives remain outside that contract and reject missing initialization
metadata. Archive/input hashes and reader source/OLean seals are unchanged. All
nine Rust integration suites and the runtime ABI probe pass. The final fresh
268-module proof closure also passes; its transitive audit covers 77,958 imported
EmptyFunction/Miri declarations with only the three allowed axioms, and the
library/example source freezes and fixed input hashes match after completion.
Fixed Rust/MIR input bytes, SHA records, theorem claims and budgets are unchanged;
these finite comparisons do not establish arbitrary coroutine or Rust safety.

### Checked coroutine conflict access

The post-merge regression workflow rejected an unchecked storage-conflict array
access in the coroutine metadata validator. The validator now uses checked
access and retains the existing invalid-index error; preceding size/index guards
make the valid path identical, including asymmetric, empty and diagonal rows.
Independent review confirmed that no validation or execution rule was relaxed.
The complete quick entry point, semantic source lint and its three unit tests,
focused coroutine controls, common 1,300-job build and 75,361-declaration axiom
audit pass. All 66 regression stages pass: stages 1–50 completed first, 51–57
after restoring a verified pinned reference binary/build record, and 58–66 after
correcting the local toolchain environment. These two setup stops are not counted
as test successes. A fresh 268-module fixed proof closure and 77,958-declaration
transitive axiom audit pass with matching library/example source freezes and
fixed input hashes. Rust/MIR bytes, SHA records, claims and budgets are unchanged.

### Performance and optimization assurance

Remaining performance work includes residual equality and validation work,
and preparation outside typed input decoding and the optimized call-resolution
lookup. Caller-location still scans its catalog; optimization must retain
source-order diagnostics, malformed-row handling and fresh Location allocations.
Measure current immutable artifacts with the protocol in [AGENTS](AGENTS.md);
old timings and shared-host samples do not establish a general speedup.
At `6a76fcbd`, hosted `pass/btreemap.rs@tree` exceeded its 900-second execution
budget. A diagnostic prefix using an immutable runner from that revision with
a newer ABI-query exporter also remained unfinished at 900 seconds after
695,759 iterations. Decode took 5.44 seconds; reported slow complete iterations included
returns, reference creation and calls. This mixed-artifact, shared-host profile
does not identify an internal CPU hotspot or establish an optimization. The
execution budget and acceptance conditions are unchanged. This does not measure
the later schema-8/indexing revisions or establish their result for this guest.
The native harness runs until a source terminal/error outcome or process
interruption, with demand-driven diagnostic choices and no scheduler-iteration,
generated-choice-count or generated-byte-length cap. Finite proof/test APIs
retain their explicit bounds. Execution still depends on host memory and on
the interpreter's demand-local capability and operation-resource checks.

No full compiler-query/decoder equivalence proof exists. Component identities
and finite guest comparisons do not imply whole-decoder equivalence or
all-choice safety. Typed pool validation establishes bounds and selected
structural invariants; it does not prove exporter/interpreter correspondence.
Native profiling identities preserve Lean states/outcomes, not native C compiler
correctness. The large catch guest still needs a fresh same-prepared-TyCtxt
reference comparison; native completion of a diagnostic trace does not prove UB
freedom over every permitted choice.

Input decoding constructs final MIR, catalog values and per-instruction facts
while parsing concrete typed tables. Integer scalar values carry their exact
compiler byte width; the reader checks their range immediately and checks width
agreement against the completed type/layout tables. Constructor shape, local
body bounds and table identities are checked during parsing. Compact numeric
MIR-reference summaries survive until table counts are known; cross-table
references, joins and required execution graphs still require completed tables.
No duplicate MIR spine, generic JSON tree or source ranges are retained. The file
entrypoint still reads a complete `String`; bounded-memory file streaming is not
implemented. Compiler table identities remain local to one input. Reusing guest
pointers or allocation identities between executions would invalidate the
execution model.

## Feature support outside the current acceptance scope

These gaps remain in the backlog, without implying that the whole feature is
unimplemented. Check existing support against pinned upstream before extending
it; preserve implementations and fail-closed Unsupported outcomes. WP remains
deferred with its implementation removed. GenMC is removed; available race
tracking modes are disabled tracking and the Miri vector-clock backend.

* **Windows / peripheral OS facilities** —
  [WindowsPlatform](Miri/Interpreter/WindowsPlatform.lean), `MiriTests/Native/`
  and Unix tests do not guarantee every target ABI, shim or real-host connection.
  Reproduce missing capabilities with a fixed target and genuine input, then
  compare shim ABI, state and errors.
* **Native guest and math boundary** — [native](native/),
  [NativeMathHost](Miri/Input/NativeMathHost.lean), `tools/NativeRunner.lean`,
  `tools/NativeMathBoundaryQA.lean` and `MiriTests/Native/`. Signaling-NaN choices,
  other widths/exponents, f128 and broader absent-host validation remain pending.
  Existing f32/f64 exponent-zero controls use fixed results and no_std
  `miri_start`, and the f64 sin(1)/cos(0) controls cover only those absent-host
  cases. They do not establish broader numerical or std-main equivalence.
  Generate references from the same Rust and compare real-host bits and
  Unsupported outcomes; helper mocks do not resolve these gaps. Separate host
  callbacks from numerical equivalence.
* **Timezone** — [source and assumptions](docs/chrono-tz-source-port.md),
  `MiriTests/Regression/TimezoneGuestEnv.lean` and `tools/check-timezone.py`.
  General host integration, all-zone/date equivalence and timestamp
  endpoint/out-of-range behavior remain unestablished. Extend genuine
  comparisons to date-range boundaries; table generation/count checks alone
  do not resolve them. Existing finite comparisons use a separate reference
  TyCtxt with isolation disabled and a retained Linux host trace; unobserved
  host demands remain Unsupported.

Alias rigidity remains a compiler syntax/state boundary: the exported boolean is
read from TyKind::Alias(IsRigid,...) rather than a dedicated query. Pinned
rustc_type_ir/ty_kind.rs documents that the new solver sets this state after
normalization and that changes to typing mode/ParamEnv invalidate it. Removing
this seed requires source alias provenance and Lean normalization/rigidification;
classifying rigidity from the alias family alone would lose semantics.

FunctionTypePrinter is now routed for local Rust-ABI FnDef diagnostics; five
additional executable signature controls cover safe/unsafe, unit output,
variadic/splat syntax and unsupported ABI rejection. JSON parsing is not kernel
reducible; these controls are executable checks, not kernel proofs.

CompilerInstanceAbi and native signature adapters now validate runtime instance
IDs against the execution-owned instance store. Their existing result catalogs
remain explicit residual domains; a new syntax identity does not create an ABI
answer. Intrinsic generic-constant operations instead read the same execution's
argument and constant nodes directly. A fresh const-generic fixture constructs
constant77 and its full instance outside both material prefixes; const_at/Value
works without a catalog row, while branch and non-Value invariants fail closed.

The new intrinsic string can be allocated with fixed CTFE salt0 before layout
checking and root adjustment; it must never be cast from runtime AllocId into
an exporter-graph ConstValue ID. The prepared allocator byte-key catalog remains
a separate migration residual: it currently probes32 salts per existing byte
image. Raw payloads alone cannot recover dedup membership because equal memory
can also receive distinct non-deduplicated IDs. Minimal exact continuation needs
actual AllocMap counter/map/dedup state access, currently private to rustc, or an
explicitly retained prepared catalog boundary. See the source-study artifact in
scratch/function-type-printer/ALLOCATION-STUDY.md.
