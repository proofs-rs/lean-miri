import duplicate_prefix.S05ZeroCellActualCallRepaired
import duplicate_prefix.S05CompletedRootSuccessExit
import duplicate_prefix.RootSuccessReleaseProfile
import duplicate_prefix.CopyRootSuccessShape

namespace DuplicatePrefix.S05ZeroCellActualCallReturn.PureTree
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05ZeroCellTypedGeneratedPrefix (tag)
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 1000000
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
/-- The repaired copy's current generated tree releases the root's buffer loan. -/
theorem release_completed :
    S05ZeroCellActualCallRepaired.PureTree.write.tree.releaseProtector (tag 8)
      S05ZeroCellActualCallRepaired.copyTracker.global.protectedTags =
    ⟨(S05ZeroCellActualCallRepaired.PureTree.write.tree.releaseProtector (tag 8)
      S05ZeroCellActualCallRepaired.copyTracker.global.protectedTags).tree,.Released⟩ := by cbv
end DuplicatePrefix.S05ZeroCellActualCallReturn.PureTree

namespace DuplicatePrefix.S05ZeroCellActualCallReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PhysicalMachineWrite
open S05ZeroCellJointPacket
open S05ZeroCellTypedGeneratedPrefix (tag)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

set_option autoImplicit false in
/-- Source-derived physical write contexts for this fixed call configuration.
These fields certify configuration wiring only, independently of machine data. -/
structure Contexts (span : PreparedContracts.FixedSpanQuery) where
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig S05ZeroCellActualCallParameters.options ()
    S05ZeroCellActualCallParameters.remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig S05ZeroCellActualCallParameters.options ()
    (S05ZeroCellActualCallParameters.remaining+1) span).access = context.access

/-- Construct both contexts from the actual configuration builder. -/
theorem contexts (span : PreparedContracts.FixedSpanQuery) : Nonempty (Contexts span) := by
  let options := S05ZeroCellActualCallParameters.options
  let remaining := S05ZeroCellActualCallParameters.remaining
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have innerFields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨outer,outerAccess,outerArithmetic,_⟩ := fields.canonicalCopy
  obtain ⟨inner,innerAccess,innerArithmetic,_⟩ := innerFields.canonicalCopy
  have outerWidth : outer.pointers.arithmetic = ⟨Size.ofBytes 8⟩ :=
    outerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () (remaining+1) span)
  have innerWidth : inner.pointers.arithmetic = ⟨Size.ofBytes 8⟩ :=
    innerArithmetic.symm.trans (CanonicalConfigFacts.actual_arithmetic options () remaining span)
  have outerRuntime : outer.access.runtime = PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) outerAccess).symm.trans
      (CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span)
  have innerRuntime : inner.access.runtime = PreparedReflection.actual.runtime.target :=
    (congrArg (fun access => access.runtime) innerAccess).symm.trans
      (CanonicalConfigFacts.actual_access_runtime options () remaining span)
  exact ⟨⟨outer,inner,innerAccess,innerWidth,(by rw [innerRuntime];rfl),
    (by rw [innerRuntime,outerRuntime]),outerWidth,(by rw [outerRuntime];rfl),
    (by rw [outerRuntime];rfl),outerAccess⟩⟩

set_option autoImplicit false in
/-- Post-copy phase data for the one fixed diagnostic packet. The generated
buffer tree and current return-slot allocation are data fields; actual release,
cleanup and physical true return are derived below. This is no caller-validity
predicate or ordinary-input coverage claim. -/
structure Input where
  options : EvalConfigurationCore.Options
  limits : ExecutionMachine.Limits
  remaining : Nat
  span : PreparedContracts.FixedSpanQuery
  source : PreparedContracts.SourceComparator
  fuel : Nat
  debugOff : options.place.debugAssertions = false
  validationFuel : options.limits.validation = fuel+1
  context : Context
  validationContext : Context
  accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access
  validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8
  sameRuntime : validationContext.access.runtime.base = context.access.runtime.base
  width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩
  runtimeWidth : context.access.runtime.base.pointerWidth = .w64
  runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8
  outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access
  before : CompilerFrameContext.ActualFrame
  after : CompilerFrameContext.ActualFrame
  pointer : Scalar Provenance
  destinationValue : Scalar Provenance
  count : UInt64
  shape : CopyRootSuccessShape.Shape before after pointer destinationValue count
  body : before.body = RootBody.reflected.body.body
  identity : before.bodyIdentity = RootBody.reflected.body.identity
  callee : before.functionInstance = RootBody.reflected.functionInstance
  noLocalClocks : before.extra.dataRace = none
  continuation : before.returnContinuation = .stop true
  varargs : before.vaList = #[]
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  tracked : machine.borrowTracker = some S05ZeroCellActualCallRepaired.copyTracker
  noClocks : machine.dataRace = none
  noBackend : machine.user.payload.payload.user.backend = .none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  thread : ThreadRecord
  active : machine.threads.activeThread? = some thread
  buffer : LocalAllocation Provenance BorrowTree MiriMemoryKind
  bufferPresent : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,buffer)
  bufferTree : buffer.allocation.extra = S05ZeroCellActualCallRepaired.PureTree.write.tree
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : machine.memory.live.find? (fun row => row.1 == destinationId) = some (destinationId,slot)
  slotTree : slot.allocation.extra = slotTree (tag 7) (tag 9) 1 true
  frameTracked : before.extra.borrowTracker = some
    ((({} : FrameState).addProtector sourceId (tag 8)).addProtector destinationId (tag 9))
  slotSize : slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : slot.allocation.len = 1
  slotMask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete destinationId (tag 7))) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat + 1 < 2^64
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == destinationId) = some ⟨destinationId,slotBase⟩
  extras : (context.extras.get machine.user).allocations.find? (fun row => row.1 == destinationId) = some (destinationId,⟨none,#[]⟩)
  destination : before.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩

noncomputable def caller (input : Input) : CompilerFrameContext.ActualFrame :=
  input.after

noncomputable def beforeReturn (input : Input) :=
  RootZeroCompleteState.tick input.options input.remaining input.span
    (RootZeroCompleteState.tick input.options input.remaining input.span input.machine)

def borrowFrame (_input : Input) :=
  ((({} : FrameState).addProtector sourceId (tag 8)).addProtector destinationId (tag 9))

noncomputable def releasedMemory (input : Input) :=
  StackPopRelease.commitTree
    (StackPopRelease.commitTree (beforeReturn input).memory sourceId input.buffer
      (S05ZeroCellActualCallRepaired.PureTree.write.tree.releaseProtector (tag 8)
        S05ZeroCellActualCallRepaired.copyTracker.global.protectedTags).tree)
    destinationId input.slot input.slot.allocation.extra

noncomputable def popped (input : Input) : MachineHooks.State MiriMemoryKind Machine.RootUser :=
  ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] (caller input)
    (ActualPopPlan.released (beforeReturn input) (releasedMemory input) S05ZeroCellActualCallRepaired.copyTracker (borrowFrame input))
    (input.thread.topUserRelevantFrame.getD 0)⟩

/-- The actual physical return target has no enclosing call frame. -/
theorem final_empty (input : Input) (updated : Allocation Provenance BorrowTree) :
    (CanonicalCopy.replaceAllocation (popped input) destinationId input.slot.kind updated).stack.frames = #[] := rfl

def Result (input : Input) : Prop :=
  let config := PreparedContracts.actualConfig input.options () (input.remaining+1) input.span
  let initial := Storage.withCurrent #[] (caller input) input.machine
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config,input.limits,fun _ _ => True⟩
  ∃ updated,
    SuccessfulTrace.Trace config input.limits initial (CanonicalCopy.replaceAllocation (popped input) destinationId input.slot.kind updated) ∧
    ExecutionMachine.step config input.limits () (CanonicalCopy.replaceAllocation (popped input) destinationId input.slot.kind updated) =
      (CanonicalCopy.replaceAllocation (popped input) destinationId input.slot.kind updated,.ok false) ∧
    CallSafety.NoUBBeforeReturn safety 1 initial ∧
    updated.extra = parentWrittenTree (tag 7) (tag 9) 1 ∧
    updated.byteSize = input.slot.allocation.byteSize ∧ updated.len = input.slot.allocation.len ∧
    updated.initializationMask = InitMask.new input.slot.allocation.byteSize true ∧
    updated.provenanceMap = ProvenanceMap.new ∧
    target_bytes input.context.access.runtime.base input.slot.allocation.byteSize 1 = .ok (AllocationCopy.snapshot updated) ∧
    updated.mutability = input.slot.allocation.mutability

set_option autoImplicit false in
private theorem row_at (frame : CompilerFrameContext.ActualFrame) (index : Nat)
    (valid : index < frame.locals.size) (row : LocalState Provenance LocalLayout)
    (known : frame.locals[index]? = some row) : frame.locals[index]'valid = row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)

set_option autoImplicit false in
/-- Complete the real root cleanup and physical true return from the data
returned by the copy helper. The source invocation/copy prefix is a separate
composition obligation; no prefix-success premise appears in this component. -/
theorem complete (input : Input) : Result input := by
  have ready : CopyRootSuccessShape.Shape input.before (caller input) input.pointer input.destinationValue input.count := input.shape
  have account := RootSuccessReleaseProfile.tick_twice_fields input.options input.remaining input.span input.machine
  change (beforeReturn input).memory = input.machine.memory ∧
    (beforeReturn input).borrowTracker = input.machine.borrowTracker ∧
    (beforeReturn input).dataRace = input.machine.dataRace ∧
    (beforeReturn input).threads = input.machine.threads ∧
    (beforeReturn input).user.addresses = input.machine.user.addresses ∧
    (beforeReturn input).user.payload.payload.user.backend = input.machine.user.payload.payload.user.backend ∧
    (beforeReturn input).user.payload.payload.user.runtime.extras = input.machine.user.payload.payload.user.runtime.extras at account
  have plan : StackPopRelease.Plan S05ZeroCellActualCallRepaired.copyTracker.global.protectedTags
      (borrowFrame input).protectedTags.toList (beforeReturn input).memory (releasedMemory input) := by
    apply StackPopRelease.Plan.live sourceId (tag 8) input.buffer
      (S05ZeroCellActualCallRepaired.PureTree.write.tree.releaseProtector (tag 8)
        S05ZeroCellActualCallRepaired.copyTracker.global.protectedTags).tree
      [(destinationId,tag 9)] (beforeReturn input).memory (releasedMemory input)
      (by rw [account.1];exact input.bufferPresent)
    · rw [input.bufferTree]
      exact PureTree.release_completed
    apply StackPopRelease.Plan.live destinationId (tag 9) input.slot input.slot.allocation.extra []
      _ (releasedMemory input)
      (StackPopRelease.lookup_commit_other _ sourceId destinationId input.buffer input.slot _
        (by decide) (by rw [account.1];exact input.slotPresent))
    · rw [input.slotTree]
      exact ReturnTreeAccess.slot_release (tag 7) (tag 9) 1 true _
        (by cbv) (by cbv) (by decide) (by decide)
    · exact .nil _
  have slotReleased : (releasedMemory input).live.find? (fun row => row.1 == destinationId) =
      some (destinationId,input.slot) := by
    have same (allocation : Allocation Provenance BorrowTree) : allocation.setExtra allocation.extra = allocation := by
      cases allocation;rfl
    simpa only [releasedMemory,same] using StackPopRelease.lookup_commit_same
      (StackPopRelease.commitTree (beforeReturn input).memory sourceId input.buffer _)
      destinationId input.slot input.slot.allocation.extra
  have popFields := RootSuccessReleaseProfile.popped_fields (caller input) (beforeReturn input) (releasedMemory input)
    S05ZeroCellActualCallRepaired.copyTracker (borrowFrame input) (input.thread.topUserRelevantFrame.getD 0)
  change (popped input).machine.memory = releasedMemory input ∧
    (popped input).machine.borrowTracker = some {S05ZeroCellActualCallRepaired.copyTracker with global := S05ZeroCellActualCallRepaired.copyTracker.global.endCall (borrowFrame input)} ∧
    (popped input).machine.user = (beforeReturn input).user ∧
    (popped input).machine.dataRace = (beforeReturn input).dataRace at popFields
  have tagsFree : (S05ZeroCellActualCallRepaired.copyTracker.global.endCall (borrowFrame input)).protectedTags.contains (tag 7) = false ∧
      (S05ZeroCellActualCallRepaired.copyTracker.global.endCall (borrowFrame input)).protectedTags.contains (tag 9) = false := by
    cbv
  have at0 := row_at (caller input) 0 (by rw [ready.size];decide) _ ready.slot0
  have at15 := row_at (caller input) 15 (by rw [ready.size];decide) _ ready.slot15
  have at17 := row_at (caller input) 17 (by rw [ready.size];decide) _ ready.slot17
  have at18 := row_at (caller input) 18 (by rw [ready.size];decide) _ ready.slot18
  have at19 := row_at (caller input) 19 (by rw [ready.size];decide) _ ready.slot19
  have at21 := row_at (caller input) 21 (by rw [ready.size];decide) _ ready.slot21
  have at24 := row_at (caller input) 24 (by rw [ready.size];decide) _ ready.slot24
  have popAddresses : (popped input).machine.user.addresses = input.machine.user.addresses :=
    (congrArg (fun user => user.addresses) popFields.2.2.1).trans account.2.2.2.2.1
  have popBackend : (popped input).machine.user.payload.payload.user.backend = .none :=
    (congrArg (fun user => user.payload.payload.user.backend) popFields.2.2.1).trans (account.2.2.2.2.2.1.trans input.noBackend)
  have popExtras : (popped input).machine.user.payload.payload.user.runtime.extras = input.machine.user.payload.payload.user.runtime.extras :=
    (congrArg (fun user => user.payload.payload.user.runtime.extras) popFields.2.2.1).trans account.2.2.2.2.2.2
  have popGhost : (popped input).machine.user.payload.ghost = false := by
    rw [popFields.2.2.1]
    change (RootZeroCompleteState.tick input.options input.remaining input.span
      (RootZeroCompleteState.tick input.options input.remaining input.span input.machine)).user.payload.ghost = false
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact input.ghost
  have popShallow : (popped input).machine.user.payload.validation = .Shallow := by
    rw [popFields.2.2.1]
    change (RootZeroCompleteState.tick input.options input.remaining input.span
      (RootZeroCompleteState.tick input.options input.remaining input.span input.machine)).user.payload.validation = .Shallow
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact input.shallow
  have maskValid : InitMaskCopy.WellFormed input.slot.allocation.initializationMask := by rw [input.slotMask];trivial
  have endpoint : (allocRange input.place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok (Size.ofBytes (input.slotBase+1)) := by
    rw [input.slotPointer]
    have added := size_add_ok (Size.ofBytes input.slotBase) (Size.ofBytes 1) (by simpa only [Size.ofBytes,UInt64.toNat_one] using input.fits)
    simp only [Pointer.new,allocRange,AllocRange.endExclusive,AllocRange.end,added,Except.mapError]
    rfl
  unfold Result
  exact S05CompletedRootSuccessExit.complete input.context input.validationContext input.options input.remaining input.span
    input.accessEq input.validationWidth input.validationRuntimeSize input.sameRuntime input.limits input.fuel input.debugOff input.validationFuel
    (caller input) input.machine (beforeReturn input) rfl input.unchecked input.noGc input.fixed S05ZeroCellActualCallRepaired.copyTracker (borrowFrame input)
    (account.2.1.trans input.tracked) (by rw [ready.extra];exact input.frameTracked)
    (releasedMemory input) plan input.thread (by rw [account.2.2.2.1];exact input.active) (popped input) rfl
    (ready.body.trans input.body) (ready.identity.trans input.identity) (ready.callee.trans input.callee) ready.location ready.size input.source
    (.scalar input.pointer) .uninit (.scalar input.pointer) (.scalar input.destinationValue) (.scalar (.fromScalarInt (.ofUInt64 input.count)))
    (congrArg (fun row => row.value) at15) (congrArg (fun row => row.value) at17) (congrArg (fun row => row.layout) at17)
    (congrArg (fun row => row.value) at18) (congrArg (fun row => row.value) at19) (congrArg (fun row => row.value) at21) (congrArg (fun row => row.value) at24)
    input.ghost input.shallow rfl (by rw [ready.size];decide) (by rw [ready.extra];exact input.noLocalClocks)
    (ready.continuation.trans input.continuation) ready.immediate (ready.varargs.trans input.varargs)
    input.place destinationId (tag 7) (tag 9) true input.slotBase 1 input.slot
    {S05ZeroCellActualCallRepaired.copyTracker with global := S05ZeroCellActualCallRepaired.copyTracker.global.endCall (borrowFrame input)}
    (congrArg (fun row => row.value) at0) (congrArg (fun row => row.layout) at0) rfl input.layout input.width (by decide) (by decide)
    (by rw [popAddresses];exact input.cached) slotReleased input.slotSize input.slotMutable maskValid input.runtimeWidth
    (by rw [input.slotStorage,input.slotSize];rfl) (by rw [input.slotMask,input.slotSize];rfl) input.slotProvenance
    (popFields.2.2.2.trans (account.2.2.1.trans input.noClocks)) popBackend popFields.2.1
    (by change (popped input).machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [popExtras];exact input.extras)
    tagsFree.1 tagsFree.2 input.slotTree input.slotPointer input.aligned input.runtimeSize input.outerAccessEq popGhost popShallow
    (by rw [ready.destination];exact input.destination) (Size.ofBytes (input.slotBase+1)) endpoint

end DuplicatePrefix.S05ZeroCellActualCallReturn
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S05ZeroCellActualCallReturn.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved fixed-packet root return dependency {dependency}"
