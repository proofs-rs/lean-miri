import duplicate_prefix.RootSuccessToReturn
import duplicate_prefix.RootZeroCompleteExitState
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootSuccessExit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open PhysicalMachineWrite
theorem complete (context validationContext : Context)
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
      (RootZeroCompleteState.tick options remaining span initialMachine))
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl initialMachine.user).gcInterval = 0)
    (fixed : initialMachine.threads.fixedScheduling = true)
    (beforeTracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (beforeTracked : beforeMachine.borrowTracker = some beforeTracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (releasedMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (plan : RootPhysicalReturnPlan.Profile beforeTracker.global.protectedTags borrowFrame.protectedTags.toList
      beforeMachine.memory releasedMemory)
    (thread : ThreadRecord) (active : beforeMachine.threads.activeThread? = some thread)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (stateEq : state = ⟨⟨#[]⟩, GenericPopFrame.afterRelevanceAt #[] frame
      (ActualPopPlan.released beforeMachine releasedMemory beforeTracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity=RootBody.reflected.body.identity)
    (callee : frame.functionInstance=RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨9,0⟩)
    (frameSize : frame.locals.size=25)
    (source : PreparedContracts.SourceComparator)
    (temp15 temp18 temp19 temp21 temp24 : Immediate Provenance)
    (live15 : (frame.locals[15]'(by omega)).value = .live (.immediate temp15))
    (live17 : (frame.locals[17]'(by omega)).value = .live (.immediate .uninit))
    (none17 : (frame.locals[17]'(by omega)).layout = none)
    (live18 : (frame.locals[18]'(by omega)).value = .live (.immediate temp18))
    (live19 : (frame.locals[19]'(by omega)).value = .live (.immediate temp19))
    (live21 : (frame.locals[21]'(by omega)).value = .live (.immediate temp21))
    (live24 : (frame.locals[24]'(by omega)).value = .live (.immediate temp24))
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
  let prefixMachine := RootZeroCompleteState.tick options remaining span initialMachine
  have initialTracked : initialMachine.borrowTracker=some beforeTracker := by
    have original := beforeTracked
    rw [beforeEq] at original
    exact original
  obtain ⟨cleaned,cleanTrace,shape⟩ :=
    RootSuccessToReturn.reaches_return options limits remaining span source debugOff fuel validationFuel #[] frame initialMachine frameSize
      temp15 temp18 temp19 temp21 temp24 live0 cached0 live15 live17 none17 live18 live19 live21 live24
      sourceBody identity callee location noLocalClocks beforeTracker initialTracked defaultMode initialGhost initialShallow unchecked noGc fixed
  let result := {cleaned with location := FrameLocation.mir ⟨10,0⟩}
  have prefixTrace : SuccessfulTrace.Trace config limits (Storage.withCurrent #[] frame initialMachine)
      (Storage.withCurrent #[] result prefixMachine) := cleanTrace
  have fsz : result.locals.size = 25 := shape.size
  have result0 := shape.output
  have fe : result.extra = frame.extra := shape.extra
  have fb : result.body = frame.body := shape.body
  have frc : result.returnContinuation = frame.returnContinuation := shape.continuation
  have fva : result.vaList = frame.vaList := shape.varargs
  have frp : result.returnPlace = frame.returnPlace := shape.destination
  have allResult : ∀ slot ∈ result.locals, ∀ memory, slot.value ≠ .live (.indirect memory) := shape.immediate immediateLocals
  have resultLocation : result.location = .mir ⟨10,0⟩ := rfl
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
    rw [beforeEq,RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact initialGhost
  have unchecked2 : (config.terminators.getControl prefixMachine.user).checkedArithmetic=false :=
    (RootZeroCompleteState.tick_flags options remaining span initialMachine).1.trans unchecked
  have noGc2 : (config.terminators.getControl prefixMachine.user).gcInterval=0 :=
    (RootZeroCompleteState.tick_flags options remaining span initialMachine).2.trans noGc
  have stateDerived : state = ⟨⟨#[]⟩,GenericPopFrame.afterRelevanceAt #[] result
      (ActualPopPlan.released beforeMachine releasedMemory beforeTracker borrowFrame) (thread.topUserRelevantFrame.getD 0)⟩ :=
    stateEq.trans (congrArg (fun machine => (⟨⟨#[]⟩,machine⟩ : MachineHooks.State MiriMemoryKind Machine.RootUser))
      (RootZeroCompleteExitState.relevance_frame_irrelevant frame result _ _))
  have releasedPresent := RootZeroCompleteExitState.profile_lookup plan id entry (by rw [beforeEq];exact initialPresent)
  have stateMemory : state.machine.memory=releasedMemory := by
    rw [stateEq]
    unfold GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have presentDerived : state.machine.memory.live.find? (fun row => row.1 == id)=some (id,entry) := by
    rw [stateMemory]
    exact releasedPresent
  obtain ⟨updated,returned,terminal,tree,bytes,len,mask,prov,encoding,mutability⟩ :=
    RootPhysicalReturn.return_step_terminal context validationContext options remaining span accessEq validationWidth validationRuntimeSize sameRuntime limits fuel debugOff validationFuel result prefixMachine beforeMachine accountedDerived unchecked2 noGc2 fixed beforeTracker borrowFrame beforeTracked (by rw [fe];exact frameTracked) releasedMemory plan thread active state stateDerived (fb.trans sourceBody) resultLocation resultValid0 (by rw [fe];exact noLocalClocks) beforeGhostDerived (frc.trans continuation) allResult (fva.trans varargs) place id root child written base count entry tracker true resultLive0 resultCached0 one layout width positive signedFits cached presentDerived size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend enabled extras rootFree childFree initialTree pointer aligned runtimeSize outerAccessEq ghost shallow (by rw [frp];exact destination) finish endpoint
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

#print axioms complete
end DuplicatePrefix.RootSuccessExit
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RootSuccessExit.complete) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved success cleanup exit safety dependency {dependency}"
