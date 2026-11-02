import duplicate_prefix.GeneralBorrowForestPhysicalReturnPlan
import duplicate_prefix.RootSuccessReleaseProfile
import duplicate_prefix.GenericRootSuccessExitCore
import duplicate_prefix.RootZeroCompletePrefix


namespace DuplicatePrefix.GeneralBorrowForestRootZeroPhysical
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PhysicalMachineWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

set_option autoImplicit false in
/-- Data at the genuine root's entry PC with count zero. The buffer release is
arbitrary multiple-root mutable/foreign/cache and activity data; release, physical return and NoUB
are derived internally. This component does not classify all caller histories. -/
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
  size : before.locals.size=25
  location : before.location=.mir ⟨0,0⟩
  slot0 : before.locals[0]?=some ⟨.live (.immediate .uninit),none⟩
  slot3 : before.locals[3]?=some ⟨.dead,none⟩
  slot4 : before.locals[4]?=some ⟨.dead,none⟩
  slot5 : before.locals[5]?=some ⟨.dead,none⟩
  slot2 : before.locals[2]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))),some RootCompilerFacts.usizeLayout⟩
  immediate : CopyHelperCleanup.AllImmediate before
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
  input.before

noncomputable def beforeReturn (input : Input) :=
  RootZeroCompleteState.tick input.options input.remaining input.span
    (RootZeroCompleteState.tick input.options input.remaining input.span
      (RootZeroCompleteState.tick input.options input.remaining input.span input.machine))

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
private theorem complete_of_plan (context validationContext : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access)
    (validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8)
    (sameRuntime : validationContext.access.runtime.base = context.access.runtime.base)
    (limits : ExecutionMachine.Limits) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (frame : CompilerFrameContext.ActualFrame)
    (initialMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (beforeEq : beforeMachine = RootZeroCompleteState.tick options remaining span
      (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span initialMachine)))
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).gcInterval = 0)
    (fixed : initialMachine.threads.fixedScheduling = true)
    (beforeTracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (beforeTracked : beforeMachine.borrowTracker = some beforeTracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan beforeTracker.global.protectedTags borrowFrame.protectedTags.toList
      beforeMachine.memory releasedMemory)
    (thread : ThreadRecord) (active : beforeMachine.threads.activeThread? = some thread)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (stateEq : state = ⟨⟨#[]⟩, GenericPopFrame.afterRelevanceAt #[] frame
      (ActualPopPlan.released beforeMachine releasedMemory beforeTracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (frameSize : frame.locals.size=25)
    (source : PreparedContracts.SourceComparator)
    (dead3 : (frame.locals[3]'(by omega)).value=.dead)
    (dead4 : (frame.locals[4]'(by omega)).value=.dead) (dead5 : (frame.locals[5]'(by omega)).value=.dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout=none) (uncached5 : (frame.locals[5]'(by omega)).layout=none)
    (live2 : (frame.locals[2]'(by omega)).value=.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))))
    (cached2 : (frame.locals[2]'(by omega)).layout=some RootCompilerFacts.usizeLayout)
    (initialGhost : initialMachine.user.payload.ghost=false)
    (initialShallow : initialMachine.user.payload.validation=.Shallow)
    (defaultMode : beforeTracker.retagMode=.Default)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (noLocalClocks : frame.extra.dataRace = none)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (live0 : frame.locals[0].value = .live (.immediate  .uninit))
    (cached0 : frame.locals[0].layout = none)
    (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (initialPresent : initialMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (releasedPresent : releasedMemory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes count)
    (mutable : entry.allocation.mutability = .Mut)
    (maskValid : InitMaskCopy.WellFormed entry.allocation.initializationMask)
    (runtimeWidth : context.access.runtime.base.pointerWidth = .w64)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (maskLength : entry.allocation.initializationMask.len = entry.allocation.byteSize)
    (provenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (noClocks : state.machine.dataRace = none)
    (noBackend : state.machine.user.payload.payload.user.backend = .none)
    (enabled : state.machine.borrowTracker = some tracker)
    (extras : (context.extras.get state.machine.user).allocations.find? (fun row => row.1 == id) = some (id,⟨none,#[]⟩))
    (rootFree : tracker.global.protectedTags.contains root = false)
    (childFree : tracker.global.protectedTags.contains child = false)
    (initialTree : entry.allocation.extra = slotTree root child count written)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id root)) (Size.ofBytes base))
    (aligned : place.mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (outerAccessEq : (PreparedContracts.actualConfig options () (remaining+1) span).access = context.access)
    (ghost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow)
    (destination : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (finish : Size) (endpoint : (allocRange place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let initial := Storage.withCurrent #[] frame initialMachine
    let contextSafety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨config,limits,fun _ _ => True⟩
    ∃ updated, SuccessfulTrace.Trace config limits initial (CanonicalCopy.replaceAllocation state id entry.kind updated) ∧
      ExecutionMachine.step config limits () (CanonicalCopy.replaceAllocation state id entry.kind updated) =
        (CanonicalCopy.replaceAllocation state id entry.kind updated,.ok false) ∧
      CallSafety.NoUBBeforeReturn contextSafety 1 initial ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize 1 = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  dsimp only
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let firstTick := RootZeroCompleteState.tick options remaining span initialMachine
  let prefixMachine := RootZeroCompleteState.tick options remaining span firstTick
  have initialTracked : initialMachine.borrowTracker=some beforeTracker := by
    have original := beforeTracked
    rw [beforeEq] at original
    exact original
  obtain ⟨result,prefixTrace,fb,fi,ff,fe,frp,frc,fva,fli,fsz,resultLocation,result0,allResult⟩ :=
    RootZeroCompletePrefix.reaches_return options limits remaining span source debugOff fuel validationFuel frame initialMachine
      sourceBody identity callee location frameSize live0 cached0 dead3 dead4 dead5 uncached4 uncached5 live2 cached2
      noLocalClocks immediateLocals beforeTracker initialTracked defaultMode initialGhost initialShallow unchecked noGc fixed
  have resultValid0 : (0:MIR.LocalId)<result.locals.size := by rw [fsz];decide
  have resultSlot0 : (result.locals[0]'resultValid0) =
      ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem resultValid0).symm.trans result0)
  have resultLive0 : (result.locals[0]'resultValid0).value=.live (.immediate (.scalar (.fromBool true))) := by rw [resultSlot0]
  have resultCached0 : (result.locals[0]'resultValid0).layout=some RootCompilerFacts.boolLayout := by rw [resultSlot0]
  have accountedDerived : beforeMachine = (SourceControl.accounted config.terminators
      (Storage.withCurrent #[] result prefixMachine)).machine := by
    rw [beforeEq]
    rfl
  have beforeGhostDerived : beforeMachine.user.payload.ghost=false := by
    rw [beforeEq,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact initialGhost
  have unchecked2 : (config.terminators.getControl prefixMachine.user).checkedArithmetic=false :=
    (RootZeroCompleteState.tick_flags options remaining span firstTick).1.trans
      ((RootZeroCompleteState.tick_flags options remaining span initialMachine).1.trans unchecked)
  have noGc2 : (config.terminators.getControl prefixMachine.user).gcInterval=0 :=
    (RootZeroCompleteState.tick_flags options remaining span firstTick).2.trans
      ((RootZeroCompleteState.tick_flags options remaining span initialMachine).2.trans noGc)
  have stateDerived : state = ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
      (ActualPopPlan.released beforeMachine releasedMemory beforeTracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩ :=
    stateEq.trans (congrArg (fun machine => (⟨⟨#[]⟩,machine⟩ : MachineHooks.State MiriMemoryKind Machine.RootUser))
      (RootZeroCompleteExitState.relevance_frame_irrelevant frame result _ _))
  have stateMemory : state.machine.memory=releasedMemory := by
    rw [stateEq]
    unfold GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have presentDerived : state.machine.memory.live.find? (fun row => row.1 == id)=some (id,entry) := by
    rw [stateMemory]
    exact releasedPresent
  obtain ⟨updated,returned,terminal,tree,bytes,len,mask,prov,encoding,mutability⟩ :=
    GenericRootPhysicalReturnCore.return_step_terminal context validationContext options remaining span accessEq validationWidth validationRuntimeSize sameRuntime limits fuel debugOff validationFuel result prefixMachine beforeMachine accountedDerived unchecked2 noGc2 fixed beforeTracker borrowFrame beforeTracked (by rw [fe];exact frameTracked) releasedMemory plan thread active state stateDerived (fb.trans sourceBody) resultLocation resultValid0 (by rw [fe];exact noLocalClocks) beforeGhostDerived (frc.trans continuation) allResult (fva.trans varargs) place id root child written base count entry tracker true resultLive0 resultCached0 one layout width positive signedFits cached presentDerived size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend enabled extras rootFree childFree initialTree pointer aligned runtimeSize outerAccessEq ghost shallow (by rw [frp];exact destination) finish endpoint
  let done := CanonicalCopy.replaceAllocation state id entry.kind updated
  have fullTrace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame initialMachine) done :=
    SuccessfulTrace.append prefixTrace (.next returned (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config,limits,fun _ _ => True⟩
  have entryCall : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] frame initialMachine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have past : CallSafety.pastCallBoundary 1 done := by
    change state.stack.frames.size<1
    rw [stateEq]
    change (0:Nat)<1
    decide
  have safe := SuccessfulTrace.no_ub safety 1 (Storage.withCurrent #[] frame initialMachine) done entryCall fullTrace past
  exact ⟨updated,fullTrace,terminal,safe,tree,bytes,len,mask,prov,encoding,mutability⟩


private theorem row_at (frame : CompilerFrameContext.ActualFrame) (index : Nat)
    (valid : index < frame.locals.size) (row : LocalState Provenance LocalLayout)
    (known : frame.locals[index]? = some row) : frame.locals[index]'valid = row :=
  Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans known)

set_option autoImplicit false in
/-- Complete the real cleanup, arbitrary-buffer protector release and physical
zero-count branch and physical true return from root PC0:0. All release and stack-pop successes are derived
from the data contract; the source invocation prefix remains a separate proof. -/
theorem complete (input : Input) : Result input := by
  have account :
      (beforeReturn input).memory=input.machine.memory ∧
      (beforeReturn input).borrowTracker=input.machine.borrowTracker ∧
      (beforeReturn input).dataRace=input.machine.dataRace ∧
      (beforeReturn input).threads=input.machine.threads ∧
      (beforeReturn input).user.addresses=input.machine.user.addresses ∧
      (beforeReturn input).user.payload.payload.user.backend=input.machine.user.payload.payload.user.backend ∧
      (beforeReturn input).user.payload.payload.user.runtime.extras=input.machine.user.payload.payload.user.runtime.extras := by
    unfold beforeReturn RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields input.options () (input.remaining+1) input.span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
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
  have at0 := row_at (caller input) 0 (by simp [caller,input.size]) _ input.slot0
  have at2 := row_at (caller input) 2 (by simp [caller,input.size]) _ input.slot2
  have at3 := row_at (caller input) 3 (by simp [caller,input.size]) _ input.slot3
  have at4 := row_at (caller input) 4 (by simp [caller,input.size]) _ input.slot4
  have at5 := row_at (caller input) 5 (by simp [caller,input.size]) _ input.slot5
  have popAddresses : (popped input).machine.user.addresses = input.machine.user.addresses :=
    (congrArg (fun user => user.addresses) popFields.2.2.1).trans account.2.2.2.2.1
  have popBackend : (popped input).machine.user.payload.payload.user.backend = .none :=
    (congrArg (fun user => user.payload.payload.user.backend) popFields.2.2.1).trans (account.2.2.2.2.2.1.trans input.noBackend)
  have popExtras : (popped input).machine.user.payload.payload.user.runtime.extras = input.machine.user.payload.payload.user.runtime.extras :=
    (congrArg (fun user => user.payload.payload.user.runtime.extras) popFields.2.2.1).trans account.2.2.2.2.2.2
  have popGhost : (popped input).machine.user.payload.ghost = false := by
    rw [popFields.2.2.1]
    change (RootZeroCompleteState.tick input.options input.remaining input.span
      (RootZeroCompleteState.tick input.options input.remaining input.span
        (RootZeroCompleteState.tick input.options input.remaining input.span input.machine))).user.payload.ghost = false
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact input.ghost
  have popShallow : (popped input).machine.user.payload.validation = .Shallow := by
    rw [popFields.2.2.1]
    change (RootZeroCompleteState.tick input.options input.remaining input.span
      (RootZeroCompleteState.tick input.options input.remaining input.span
        (RootZeroCompleteState.tick input.options input.remaining input.span input.machine))).user.payload.validation = .Shallow
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact input.shallow
  have maskValid : InitMaskCopy.WellFormed input.release.slot.allocation.initializationMask := by rw [input.slotMask];trivial
  have endpoint : (allocRange input.place.mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok (Size.ofBytes (input.slotBase+1)) := by
    rw [input.slotPointer]
    have added := size_add_ok (Size.ofBytes input.slotBase) (Size.ofBytes 1) (by simpa only [Size.ofBytes,UInt64.toNat_one] using input.fits)
    simp only [Pointer.new,allocRange,AllocRange.endExclusive,AllocRange.end,added,Except.mapError]
    rfl
  unfold Result
  exact complete_of_plan input.context input.validationContext input.options input.remaining input.span
    input.accessEq input.validationWidth input.validationRuntimeSize input.sameRuntime input.limits input.fuel input.debugOff input.validationFuel
    (caller input) input.machine (beforeReturn input) rfl input.unchecked input.noGc input.fixed input.tracker (borrowFrame input)
    (account.2.1.trans input.tracked) input.frameTracked
    (releasedMemory input) plan input.thread (by rw [account.2.2.2.1];exact input.active) (popped input) rfl
    input.body input.identity input.callee input.location input.size input.source
    (congrArg (fun row => row.value) at3) (congrArg (fun row => row.value) at4) (congrArg (fun row => row.value) at5)
    (congrArg (fun row => row.layout) at4) (congrArg (fun row => row.layout) at5)
    (congrArg (fun row => row.value) at2) (congrArg (fun row => row.layout) at2)
    input.ghost input.shallow input.defaultMode (by simp [caller,input.size]) input.noLocalClocks
    input.continuation input.immediate input.varargs
    input.place input.release.slotId input.release.slotRoot input.release.slotChild true input.slotBase 1 input.release.slot
    {input.tracker with global := input.tracker.global.endCall (borrowFrame input)}
    (congrArg (fun row => row.value) at0) (congrArg (fun row => row.layout) at0) rfl input.layout input.width (by decide) (by decide)
    (by rw [popAddresses];exact input.cached) input.release.slotPresent (GeneralBorrowForestPhysicalReturnPlan.slot_lookup input.release) input.slotSize input.slotMutable maskValid input.runtimeWidth
    (by rw [input.slotStorage,input.slotSize];rfl) (by rw [input.slotMask,input.slotSize];rfl) input.slotProvenance
    (popFields.2.2.2.trans (account.2.2.1.trans input.noClocks)) popBackend popFields.2.1
    (by change (popped input).machine.user.payload.payload.user.runtime.extras.allocations.find? _ = _;rw [popExtras];exact input.extras)
    tagsFree.1 tagsFree.2 input.release.slotTree input.slotPointer input.aligned input.runtimeSize input.outerAccessEq popGhost popShallow
    input.destination (Size.ofBytes (input.slotBase+1)) endpoint

end DuplicatePrefix.GeneralBorrowForestRootZeroPhysical
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GeneralBorrowForestRootZeroPhysical.complete) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved forest copied-root physical exit dependency {dependency}"
