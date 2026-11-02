import duplicate_prefix.GeneralBorrowForestPhysicalReturnPlan
import duplicate_prefix.RootSuccessReleaseProfile
import duplicate_prefix.GenericRootSuccessExitCore
import duplicate_prefix.CopyRootSuccessShape


namespace DuplicatePrefix.GeneralBorrowForestAcceptedPhysicalExit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

set_option autoImplicit false in
/-- Post-copy data and the physical return-release.slot contract. The fields supplied by
`CopyRootComplete` describe its result; no operation-success proposition occurs
in this interface. The theorem below begins at the restored root caller. -/
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
  ready : CompilerFrameContext.ActualFrame
  pointer : Scalar Provenance
  destinationValue : Scalar Provenance
  count : UInt64
  shape : CopyRootSuccessShape.Shape before ready pointer destinationValue count
  body : before.body = RootBody.reflected.body.body
  identity : before.bodyIdentity = RootBody.reflected.body.identity
  callee : before.functionInstance = RootBody.reflected.functionInstance
  noLocalClocks : before.extra.dataRace = none
  continuation : before.returnContinuation = .stop true
  varargs : before.vaList = #[]
  machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  tracker : MachineHooks.BorrowState
  tracked : machine.borrowTracker = some tracker
  defaultMode : tracker.retagMode = .Default
  noClocks : machine.dataRace = none
  noBackend : machine.user.payload.payload.user.backend = .none
  ghost : machine.user.payload.ghost = false
  shallow : machine.user.payload.validation = .Shallow
  unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false
  noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0
  fixed : machine.threads.fixedScheduling = true
  thread : ThreadRecord
  active : machine.threads.activeThread? = some thread
  release : GeneralBorrowForestPhysicalReturnPlan.Input machine.memory tracker.global.protectedTags
  frameTracked : before.extra.borrowTracker = some (GeneralBorrowForestPhysicalReturnPlan.frame release)
  slotSize : release.slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : release.slot.allocation.len = 1
  slotMask : release.slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : release.slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : release.slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete release.slotId release.slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat + 1 < 2^64
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == release.slotId) = some ⟨release.slotId,slotBase⟩
  extras : (context.extras.get machine.user).allocations.find? (fun row => row.1 == release.slotId) = some (release.slotId,⟨none,#[]⟩)
  destination : before.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩

noncomputable def caller (input : Input) : CompilerFrameContext.ActualFrame :=
  input.ready

noncomputable def beforeReturn (input : Input) :=
  RootZeroCompleteState.tick input.options input.remaining input.span
    (RootZeroCompleteState.tick input.options input.remaining input.span input.machine)

def borrowFrame (input : Input) := GeneralBorrowForestPhysicalReturnPlan.frame input.release

noncomputable def releasedMemory (input : Input) :=
  GeneralBorrowForestPhysicalReturnPlan.releasedMemory input.release

noncomputable def popped (input : Input) : MachineHooks.State MiriMemoryKind Machine.RootUser :=
  ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] (caller input)
    (ActualPopPlan.released (beforeReturn input) (releasedMemory input) input.tracker (borrowFrame input))
    (input.thread.topUserRelevantFrame.getD 0)⟩

def Result (input : Input) : Prop :=
  let config := PreparedContracts.actualConfig input.options () (input.remaining+1) input.span
  let initial := Storage.withCurrent #[] (caller input) input.machine
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config,input.limits,fun _ _ => True⟩
  ∃ updated,
    SuccessfulTrace.Trace config input.limits initial (CanonicalCopy.replaceAllocation (popped input) input.release.slotId input.release.slot.kind updated) ∧
    ExecutionMachine.step config input.limits () (CanonicalCopy.replaceAllocation (popped input) input.release.slotId input.release.slot.kind updated) =
      (CanonicalCopy.replaceAllocation (popped input) input.release.slotId input.release.slot.kind updated,.ok false) ∧
    CallSafety.NoUBBeforeReturn safety 1 initial ∧
    updated.extra = parentWrittenTree input.release.slotRoot input.release.slotChild 1 ∧
    updated.byteSize = input.release.slot.allocation.byteSize ∧ updated.len = input.release.slot.allocation.len ∧
    updated.initializationMask = InitMask.new input.release.slot.allocation.byteSize true ∧
    updated.provenanceMap = ProvenanceMap.new ∧
    target_bytes input.context.access.runtime.base input.release.slot.allocation.byteSize 1 = .ok (AllocationCopy.snapshot updated) ∧
    updated.mutability = input.release.slot.allocation.mutability

set_option autoImplicit false in
private theorem row_at (frame : CompilerFrameContext.ActualFrame) (index : Nat)
    (valid : index < frame.locals.size) (row : LocalState Provenance LocalLayout)
    (known : frame.locals[index]? = some row) : frame.locals[index]'valid = row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)

set_option autoImplicit false in
/-- Complete the real cleanup, arbitrary-buffer protector release and physical
true return from root PC9:0. All release and stack-pop successes are derived
from the data contract; the source invocation prefix remains a separate proof. -/
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
  have plan : StackPopRelease.Plan input.tracker.global.protectedTags (borrowFrame input).protectedTags.toList
      (beforeReturn input).memory (releasedMemory input) := by
    rw [account.1]
    exact GeneralBorrowForestPhysicalReturnPlan.to_plan input.release
  have popFields := RootSuccessReleaseProfile.popped_fields (caller input) (beforeReturn input) (releasedMemory input)
    input.tracker (borrowFrame input) (input.thread.topUserRelevantFrame.getD 0)
  change (popped input).machine.memory = releasedMemory input ∧
    (popped input).machine.borrowTracker = some {input.tracker with global := input.tracker.global.endCall (borrowFrame input)} ∧
    (popped input).machine.user = (beforeReturn input).user ∧
    (popped input).machine.dataRace = (beforeReturn input).dataRace at popFields
  have tagsFree : (input.tracker.global.endCall (borrowFrame input)).protectedTags.contains input.release.slotRoot = false ∧
      (input.tracker.global.endCall (borrowFrame input)).protectedTags.contains input.release.slotChild = false := by
    constructor
    · rw [StackPopRelease.end_call_contains]
      split
      · rfl
      · exact input.release.slotRootFree
    · rw [StackPopRelease.end_call_contains]
      simp [borrowFrame,GeneralBorrowForestPhysicalReturnPlan.frame,FrameState.addProtector]
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
  have maskValid : InitMaskCopy.WellFormed input.release.slot.allocation.initializationMask := by rw [input.slotMask];trivial
  have endpoint : (allocRange input.place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok (Size.ofBytes (input.slotBase+1)) := by
    rw [input.slotPointer]
    have added := size_add_ok (Size.ofBytes input.slotBase) (Size.ofBytes 1) (by simpa only [Size.ofBytes,UInt64.toNat_one] using input.fits)
    simp only [Pointer.new,allocRange,AllocRange.endExclusive,AllocRange.end,added,Except.mapError]
    rfl
  unfold Result
  exact GenericRootSuccessExitCore.complete input.context input.validationContext input.options input.remaining input.span
    input.accessEq input.validationWidth input.validationRuntimeSize input.sameRuntime input.limits input.fuel input.debugOff input.validationFuel
    (caller input) input.machine (beforeReturn input) rfl input.unchecked input.noGc input.fixed input.tracker (borrowFrame input)
    (account.2.1.trans input.tracked) (by rw [ready.extra];exact input.frameTracked)
    (releasedMemory input) plan input.thread (by rw [account.2.2.2.1];exact input.active) (popped input) rfl
    (ready.body.trans input.body) (ready.identity.trans input.identity) (ready.callee.trans input.callee) ready.location ready.size input.source
    (.scalar input.pointer) .uninit (.scalar input.pointer) (.scalar input.destinationValue) (.scalar (.fromScalarInt (.ofUInt64 input.count)))
    (congrArg (fun row => row.value) at15) (congrArg (fun row => row.value) at17) (congrArg (fun row => row.layout) at17)
    (congrArg (fun row => row.value) at18) (congrArg (fun row => row.value) at19) (congrArg (fun row => row.value) at21) (congrArg (fun row => row.value) at24)
    input.ghost input.shallow input.defaultMode (by rw [ready.size];decide) (by rw [ready.extra];exact input.noLocalClocks)
    (ready.continuation.trans input.continuation) ready.immediate (ready.varargs.trans input.varargs)
    input.place input.release.slotId input.release.slotRoot input.release.slotChild true input.slotBase 1 input.release.slot
    {input.tracker with global := input.tracker.global.endCall (borrowFrame input)}
    (congrArg (fun row => row.value) at0) (congrArg (fun row => row.layout) at0) rfl input.layout input.width (by decide) (by decide)
    (by rw [popAddresses];exact input.cached) input.release.slotPresent (GeneralBorrowForestPhysicalReturnPlan.slot_lookup input.release) input.slotSize input.slotMutable maskValid input.runtimeWidth
    (by rw [input.slotStorage,input.slotSize];rfl) (by rw [input.slotMask,input.slotSize];rfl) input.slotProvenance
    (popFields.2.2.2.trans (account.2.2.1.trans input.noClocks)) popBackend popFields.2.1
    (by change (popped input).machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [popExtras];exact input.extras)
    tagsFree.1 tagsFree.2 input.release.slotTree input.slotPointer input.aligned input.runtimeSize input.outerAccessEq popGhost popShallow
    (by rw [ready.destination];exact input.destination) (Size.ofBytes (input.slotBase+1)) endpoint

end DuplicatePrefix.GeneralBorrowForestAcceptedPhysicalExit
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GeneralBorrowForestAcceptedPhysicalExit.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved copied-root physical exit dependency {dependency}"
