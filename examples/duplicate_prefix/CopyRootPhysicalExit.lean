import duplicate_prefix.CopyRootExitData
import duplicate_prefix.CopyRootSuccessShape
import duplicate_prefix.RootSuccessExit

namespace DuplicatePrefix.CopyRootPhysicalExit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

set_option autoImplicit false in
/-- Post-copy data and the physical return-slot contract. The fields supplied by
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
  preCopy : CompilerFrameContext.ActualFrame
  pointer : Scalar Provenance
  destinationValue : Scalar Provenance
  count : UInt64
  shape : PositiveRootSuccessProfile.FrameShape before preCopy pointer destinationValue count
  zero : before.locals[0]? = some ⟨.live (.immediate .uninit),none⟩
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
  memoryBeforeCopy : MemoryState Provenance BorrowTree MiriMemoryKind
  id : AllocId
  kind : MemoryKind MiriMemoryKind
  allocation : Allocation Provenance BorrowTree
  copied : Allocation Provenance BorrowTree
  memory : machine.memory = CopyHelperCall.memoryAfter memoryBeforeCopy id kind copied
  tags : Fin 6 → BorTag
  distinct : Function.Injective tags
  mask : ProtectedBorrowAccess.SixMask tags tracker.global.protectedTags false
  tag : BorTag
  tagAt : tag = tags 5
  offset : UInt64
  len : UInt64
  positive : (0 : UInt64) < count
  bounds : offset.toNat + len.toNat ≤ allocation.byteSize.bytes.toNat
  copyBounds : count.toNat + count.toNat ≤ len.toNat
  initial : allocation.extra = NestedBorrowAccess.nestedTree tags
    (BorrowRangeAccess.partitionWithInside allocation.byteSize.bytes offset (offset+len)
      BorrowRangeAccess.rootLocation (NestedBorrowAccess.nestedLocation false))
  copiedTree : copied.extra =
    ((allocation.extra.performBorrowAccessRange (.concrete tag) (Size.ofBytes offset) (Size.ofBytes count)
        .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree.performBorrowAccessRange
      (.concrete tag) (Size.ofBytes (offset+count)) (Size.ofBytes count) .Write tracker.global.protectedTags .VisitChildrenOfAccessed).tree
  slotId : AllocId
  separate : slotId ≠ id
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : memoryBeforeCopy.live.find? (fun row => row.1 == slotId) = some (slotId,slot)
  slotRoot : BorTag
  slotChild : BorTag
  slotTree : slot.allocation.extra = slotTree slotRoot slotChild 1 true
  slotRootFree : tracker.global.protectedTags.contains slotRoot = false
  slotChildHeld : tracker.global.protectedTags.contains slotChild = true
  slotDistinct : slotRoot ≠ slotChild
  frameTracked : before.extra.borrowTracker = some (RootSuccessReleaseProfile.frame id tags slotId slotChild)
  slotSize : slot.allocation.byteSize = Size.ofBytes 1
  slotStorage : slot.allocation.len = 1
  slotMask : slot.allocation.initializationMask = InitMask.new (Size.ofBytes 1) false
  slotProvenance : slot.allocation.provenanceMap = ProvenanceMap.new
  slotMutable : slot.allocation.mutability = .Mut
  place : MPlaceTy Provenance
  layout : place.layout = RootCompilerFacts.boolLayout
  slotBase : UInt64
  slotPointer : place.mplace.ptr = Pointer.new (some (.concrete slotId slotRoot)) (Size.ofBytes slotBase)
  aligned : place.mplace.misaligned = none
  fits : slotBase.toNat + 1 < 2^64
  cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == slotId) = some ⟨slotId,slotBase⟩
  extras : (context.extras.get machine.user).allocations.find? (fun row => row.1 == slotId) = some (slotId,⟨none,#[]⟩)
  destination : before.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩

noncomputable def caller (input : Input) : CompilerFrameContext.ActualFrame :=
  CopyRootOutput.caller input.preCopy (by rw [input.shape.size];decide)

noncomputable def beforeReturn (input : Input) :=
  RootZeroCompleteState.tick input.options input.remaining input.span
    (RootZeroCompleteState.tick input.options input.remaining input.span input.machine)

def borrowFrame (input : Input) := RootSuccessReleaseProfile.frame input.id input.tags input.slotId input.slotChild

noncomputable def releasedMemory (input : Input) :=
  RootSuccessReleaseProfile.releasedMemory (beforeReturn input).memory input.id ⟨input.kind,input.copied⟩ input.slotId input.slot

noncomputable def popped (input : Input) : MachineHooks.State MiriMemoryKind Machine.RootUser :=
  ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] (caller input)
    (ActualPopPlan.released (beforeReturn input) (releasedMemory input) input.tracker (borrowFrame input))
    (input.thread.topUserRelevantFrame.getD 0)⟩

def Result (input : Input) : Prop :=
  let config := PreparedContracts.actualConfig input.options () (input.remaining+1) input.span
  let initial := Storage.withCurrent #[] (caller input) input.machine
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config,input.limits,fun _ _ => True⟩
  ∃ updated,
    SuccessfulTrace.Trace config input.limits initial (CanonicalCopy.replaceAllocation (popped input) input.slotId input.slot.kind updated) ∧
    ExecutionMachine.step config input.limits () (CanonicalCopy.replaceAllocation (popped input) input.slotId input.slot.kind updated) =
      (CanonicalCopy.replaceAllocation (popped input) input.slotId input.slot.kind updated,.ok false) ∧
    CallSafety.NoUBBeforeReturn safety 1 initial ∧
    updated.extra = parentWrittenTree input.slotRoot input.slotChild 1 ∧
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
  have ready : CopyRootSuccessShape.Shape input.before (caller input) input.pointer input.destinationValue input.count := CopyRootSuccessShape.of_copy input.before input.preCopy input.pointer input.destinationValue input.count
    input.shape input.zero (by rw [input.shape.size];decide)
  have account := RootSuccessReleaseProfile.tick_twice_fields input.options input.remaining input.span input.machine
  change (beforeReturn input).memory = input.machine.memory ∧
    (beforeReturn input).borrowTracker = input.machine.borrowTracker ∧
    (beforeReturn input).dataRace = input.machine.dataRace ∧
    (beforeReturn input).threads = input.machine.threads ∧
    (beforeReturn input).user.addresses = input.machine.user.addresses ∧
    (beforeReturn input).user.payload.payload.user.backend = input.machine.user.payload.payload.user.backend ∧
    (beforeReturn input).user.payload.payload.user.runtime.extras = input.machine.user.payload.payload.user.runtime.extras at account
  have data := CopyRootExitData.from_copy input.memoryBeforeCopy input.machine.memory input.id input.slotId input.separate input.kind
    input.allocation input.copied input.memory input.slot input.slotPresent input.tags input.distinct input.tracker.global.protectedTags input.mask
    input.tag input.tagAt input.offset input.len input.count input.positive input.bounds input.copyBounds input.initial input.copiedTree
    input.slotRoot input.slotChild input.slotTree input.slotRootFree input.slotChildHeld input.slotDistinct
  have plan : RootPhysicalReturnPlan.Profile input.tracker.global.protectedTags (borrowFrame input).protectedTags.toList
      (beforeReturn input).memory (releasedMemory input) := by
    dsimp only [releasedMemory,borrowFrame]
    rw [account.1]
    exact data.2.2.2.1
  have popFields := RootSuccessReleaseProfile.popped_fields (caller input) (beforeReturn input) (releasedMemory input)
    input.tracker (borrowFrame input) (input.thread.topUserRelevantFrame.getD 0)
  change (popped input).machine.memory = releasedMemory input ∧
    (popped input).machine.borrowTracker = some {input.tracker with global := input.tracker.global.endCall (borrowFrame input)} ∧
    (popped input).machine.user = (beforeReturn input).user ∧
    (popped input).machine.dataRace = (beforeReturn input).dataRace at popFields
  have tagsFree := RootSuccessReleaseProfile.slot_tags_after_release input.tracker.global input.id input.slotId input.tags
    input.slotRoot input.slotChild input.slotRootFree
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
  exact RootSuccessExit.complete input.context input.validationContext input.options input.remaining input.span
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
    input.place input.slotId input.slotRoot input.slotChild true input.slotBase 1 input.slot
    {input.tracker with global := input.tracker.global.endCall (borrowFrame input)}
    (congrArg (fun row => row.value) at0) (congrArg (fun row => row.layout) at0) rfl input.layout input.width (by decide) (by decide)
    (by rw [popAddresses];exact input.cached) data.2.1 input.slotSize input.slotMutable maskValid input.runtimeWidth
    (by rw [input.slotStorage,input.slotSize];rfl) (by rw [input.slotMask,input.slotSize];rfl) input.slotProvenance
    (popFields.2.2.2.trans (account.2.2.1.trans input.noClocks)) popBackend popFields.2.1
    (by change (popped input).machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [popExtras];exact input.extras)
    tagsFree.1 tagsFree.2 input.slotTree input.slotPointer input.aligned input.runtimeSize input.outerAccessEq popGhost popShallow
    (by rw [ready.destination];exact input.destination) (Size.ofBytes (input.slotBase+1)) endpoint

end DuplicatePrefix.CopyRootPhysicalExit
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.CopyRootPhysicalExit.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved copied-root physical exit dependency {dependency}"
