import duplicate_prefix.CandidateCurrentFnEntryRaw
import duplicate_prefix.CandidateCurrentGrantRuntime
import duplicate_prefix.OrdinaryPhysicalValidity
import duplicate_prefix.DuplicatePrefixTypeCacheOrigins

/-! REVIEWABLE PROPOSAL for one current call, not an adopted definition of
ordinary current-call validity for the fixed interpreter. The three records separate current Freeze entitlements,
actual argument/storage correspondence, and interpreter representation/settings.
No field asserts access success, a future permission table, NoUB, or a history.
The final theorem consumes this proposal only for the positive borrowing stage.

Admission still needs an independent argument: in particular current exposed
origin/completed-ancestry choice, copy-family identity and protector commitments
must describe the intended ordinary domain. Their inclusion here does not prove
necessity or coverage. No historical loan-parent closure is imposed on unused
suspended annotations. Whole-machine frame installation and typed MIR execution
are not conclusions. -/
namespace DuplicatePrefix.CurrentCallAdmission
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
set_option autoImplicit false

/-- Available Freeze contents are charged to named current owners. Suspended
charges coexist with active ones; only active readers may share a byte. Cell
and inactive raw grants create no Freeze charge merely by existing. The two
ABI roles are distinct owners, but their pointers/grants/allocations may agree
when the physical footprints do not overlap. The role equations fix only the
source .mut and return .ret ACTIVE footprints; they impose no closure on other
modes or suspended annotations associated with those owners.

Every active charge has ONE fixed instance and completion. For each actual
raw segment, ancestor grants supply the demanded token, while any automatically
decoded protector guard that clashes with the demand must belong to that same
completed ancestry. A retained revoked tombstone therefore remains observable;
an inactive alias or ambient Cell grant is not globally excluded. These are
current resource statements, not an operational permission/success premise. -/
structure ActiveFreezeContents (before : Before) (tracker : MachineHooks.BorrowState)
    (call : CallLoans) (data : Identities) : Prop where
  distinctRoles : call.sourceOwner ≠ call.returnOwner
  sourceContents : ∀ byte,
    data.interpretation.content byte call.sourceOwner = some ⟨.mut,.active⟩ ↔
      Window call.sourceId call.sourceOffset call.length byte
  returnContents : ∀ byte,
    data.interpretation.content byte call.returnOwner = some ⟨.ret,.active⟩ ↔
      Window call.returnId call.returnOffset 1 byte
  compatible : ∀ byte first second firstCharge secondCharge, first ≠ second →
    data.interpretation.content byte first = some firstCharge →
    data.interpretation.content byte second = some secondCharge →
    CandidateFreezeContentResources.Compatible firstCharge secondCharge
  activeGrants : ∀ byte owner mode,
    data.interpretation.content byte owner = some ⟨mode,.active⟩ →
    ∃ loan pointer allocation precise,
      data.interpretation.loans[owner]? = some loan ∧
      data.interpretation.pointers[loan.pointer]? = some pointer ∧
      pointer.allocation = byte.1 ∧ Present (ActualWorld before) byte.1 allocation ∧
      byte.2 < allocation.len ∧ (byte.1,precise) ∈ data.interpretation.precise.toList ∧
      ∀ segment ∈ allocation.extra.locations.entries.toList,
        segment.range.start.toNat ≤ byte.2 → byte.2 < segment.range.stop.toNat →
        ∀ index node, allocation.extra.nodes.get index = some node →
          (Below precise.completion index pointer.grant →
            demandOf mode ∈ tokens (denote (RawState segment.data index node)
              (tracker.global.protectedTags.contains node.tag))) ∧
          (Clash (guard (denote (RawState segment.data index node)
              (tracker.global.protectedTags.contains node.tag))) (demandOf mode) →
            Below precise.completion index pointer.grant)

/-- The source's physical value conditions are separate from its content right.
The empty alternative authorizes nonnull zero-size metadata, including integer
encodings without provenance, without demanding any live source allocation,
source loan, or source origin. The positive alternative includes initialized u8
bytes, writable backing, signed-size and physical bounds; actual provenance and
address normalization are supplied by ActualCallStorage below. -/
def SourceStorage (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (call : CallLoans) : Prop :=
  (len = 0 ∧ DuplicatePrefixEmptyReferenceInput.Candidate
    (DuplicatePrefixCallSpecification.imageContext options before tracker)
    before.memory before.user.addresses (DuplicatePrefixSliceArgument.placePointer argument)) ∨
  (len ≠ 0 ∧ ∃ allocation, Present (ActualWorld before) call.sourceId allocation ∧
    OrdinaryPhysicalValidity.MutU8Slice allocation (UInt64.ofNat call.sourceOffset) len)

/-- Current ABI-role correspondence and physical storage. Listed annotations
are internally consistent with interpretation values; source and return machine
values are bound separately. Actual provenance of arbitrary program copies is
not reconstructed. Equal bits do not merge instance identities.
Normalized windows retain the actual cached base, provenance and interior offset;
this is an explicit address-representation boundary whose admission is open.
A positive integer-only source cannot satisfy the actual pointer branch.

Bool backing may be uninitialized, since the call will overwrite it. Its layout,
alignment, mutability and one-byte containment are separate from Freeze rights.
No source/return allocation inequality, root shape or outside-window permission
restriction occurs. When length is zero the source instance clause is vacuous;
its content window is empty by the independent length equality. -/
structure ActualCallStorage (options : EvalConfigurationCore.Options) (before : Before)
    (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities) : Prop where
  protectors : before.borrowTracker.map (fun actual => actual.global.protectedTags) =
    some tracker.global.protectedTags
  length : call.length = len.toNat
  listedCopies : StableChoices data
  instances : ∀ pointer ∈ data.interpretation.pointers.toList, ∃ allocation,
    Present (ActualWorld before) pointer.allocation allocation ∧ PointerBinds allocation pointer
  sourceArgument : 0 < len.toNat → ∃ loan pointer,
    data.interpretation.loans[call.sourceOwner]? = some loan ∧
    data.interpretation.pointers[loan.pointer]? = some pointer ∧
    pointer.allocation = call.sourceId ∧ argument = .pointer pointer.value
  returnPlace : place.layout = RootCompilerFacts.boolLayout ∧ ∃ loan pointer,
    data.interpretation.loans[call.returnOwner]? = some loan ∧
    data.interpretation.pointers[loan.pointer]? = some pointer ∧
    pointer.allocation = call.returnId ∧ place.mplace.ptr = pointer.value.withOptionalProvenance
  sourceAddress : CandidateCallBindings.SourceBinding before data.interpretation call argument len
  returnAddress : CandidateCallBindings.ReturnBinding before data.interpretation call place
  sourceValue : SourceStorage options before tracker argument len call
  returnValue : ∃ allocation, Present (ActualWorld before) call.returnId allocation ∧
    OrdinaryPhysicalValidity.BoolDestination allocation (UInt64.ofNat call.returnOffset)
  returnAligned : place.mplace.misaligned = none

/-- Machine-side representation and the selected interpreter scope. Completion
records current physical and chosen exposed-origin ancestry, not permission
success. Precise row dimensions are explicit representation data; no equality
between raw tables and selected precise permission rows is required.

Runtime possible/profile facts derive scalar realization, including the absence
of lazy Unique and held ReservedIM rows; realization is not an extra ownership
restriction. All-live resource tag bounds matter even when the return allocation
differs from the source. Numeric/fuel margins and selected settings are not
claimed to be necessary for ordinary validity. Admission of completed origins,
address/tree exposure coherence, settings and budgets remains explicit work. -/
structure MachineRepresentation (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (tracker : MachineHooks.BorrowState) (len : UInt64) (data : Identities) : Prop where
  worldIds : ((ActualWorld before).toList.map Prod.fst).Nodup
  completionIds : (data.interpretation.precise.toList.map Prod.fst).Nodup
  completed : ∀ id precise, (id,precise) ∈ data.interpretation.precise.toList → ∃ allocation,
    Present (ActualWorld before) id allocation ∧ Completes allocation.extra precise.completion ∧
    precise.states.size = allocation.len ∧
    ∀ row ∈ precise.states.toList, row.size = allocation.extra.nodes.data.size
  /-- Array constructor identities must not shadow compiler non-array types.
  This permits populated canonical caches; target-ID absence is derived from
  origin/catalog consistency, rather than required as an ownership premise.
  Admission of this current representation invariant remains open. -/
  cacheOrigins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types
  state : DuplicatePrefixRuntimeInput.OrderedState before tracker
  settings : DuplicatePrefixCallModel.Model options remaining span before
  resources : DuplicatePrefixCallSpecification.Resources options limits remaining before tracker len

/-- REVIEWABLE PROPOSED domain, deliberately not named Ordinary or ValidInput.
This makes the currently proposed clauses inspectable; it does not certify their
admission. It neither assumes a preexisting callee frame nor a caller history. -/
structure Proposed (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (len : UInt64) (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities) : Prop where
  contents : ActiveFreezeContents before tracker call data
  actual : ActualCallStorage options before tracker argument len place call data
  machine : MachineRepresentation options limits remaining span before tracker len data

/-- The older Joint API is a derived implementation-facing view of the exposed
resource clauses. Scalar realization comes from the independent runtime layer. -/
theorem Proposed.joint {options limits remaining span before tracker argument len place call data}
    (input : Proposed options limits remaining span before tracker argument len place call data) :
    Joint (ActualWorld before) tracker.global.protectedTags data.interpretation := by
  refine ⟨⟨input.machine.worldIds,input.machine.completionIds,input.machine.completed⟩,
    input.contents.compatible, CandidateCurrentGrantRuntime.actual_state before tracker input.machine.state.toState,?_⟩
  intro byte owner mode active
  exact input.contents.activeGrants byte owner mode active

theorem Proposed.claims {options limits remaining span before tracker argument len place call data}
    (input : Proposed options limits remaining span before tracker argument len place call data) :
    Claims data.interpretation call :=
  ⟨input.contents.distinctRoles,input.contents.sourceContents,input.contents.returnContents⟩

theorem Proposed.actualBindings {options limits remaining span before tracker argument len place call data}
    (input : Proposed options limits remaining span before tracker argument len place call data) :
    ActualBindings before argument len place tracker.global.protectedTags call data :=
  ⟨input.actual.protectors,input.actual.length,input.actual.listedCopies,input.actual.instances,
    input.actual.sourceArgument,input.actual.returnPlace⟩

theorem Proposed.normalizedWindows {options limits remaining span before tracker argument len place call data}
    (input : Proposed options limits remaining span before tracker argument len place call data) :
    NormalizedWindows before argument len place call data :=
  ⟨input.actual.sourceAddress,input.actual.returnAddress⟩

/-- The proposed current clauses imply the existing positive borrowing theorem.
The callee's new FnEntry frame is supplied here: it need not already occur in
Before. This theorem does not install it or establish whole-call/typed safety.
Physical source/Bool validity and selected settings remain inspectable domain
clauses even though this isolated Tree Borrows stage does not consume them. -/
theorem Proposed.positive_fnentry {options limits remaining span before tracker argument len place call data}
    (input : Proposed options limits remaining span before tracker argument len place call data)
    (frame : FrameState) (positive : 0 < len.toNat) :
    Nonempty (CandidateCurrentFnEntryRaw.Result before tracker frame argument len place call data) :=
  CandidateCurrentFnEntryRaw.invoke options limits remaining before tracker frame argument len place call data
    input.joint input.actualBindings input.normalizedWindows input.claims positive input.machine.state input.machine.resources

end DuplicatePrefix.CurrentCallAdmission

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallAdmission." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved proposed current admission dependency {dependency}"
