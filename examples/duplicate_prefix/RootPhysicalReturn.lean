import duplicate_prefix.RootPhysicalReturnSupport
import duplicate_prefix.RootPhysicalReturnPlan
import duplicate_prefix.RootZeroBranch
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootPhysicalReturn
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input Miri.Concurrency
open PhysicalMachineWrite
theorem driver (context validationContext : Context)
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (accessEq : (PreparedContracts.actualConfig options () remaining span).access = validationContext.access)
    (validationWidth : validationContext.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (validationRuntimeSize : validationContext.access.runtime.pointerSize = Size.ofBytes 8)
    (sameRuntime : validationContext.access.runtime.base = context.access.runtime.base)
    (limits : ExecutionMachine.Limits) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (frame : CompilerFrameContext.ActualFrame)
    (beforeMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
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
    (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (noLocalClocks : frame.extra.dataRace = none)
    (beforeGhost : beforeMachine.user.payload.ghost = false)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (value : Bool)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
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
    ∃ updated, ControlFlow.returnFromCurrentFrame
      (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining+1) span) limits) () false
      (Storage.withCurrent #[] frame beforeMachine) =
      ({state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}},.ok ()) ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let control := GenericCallReturn.sourceControl config limits
  let before := Storage.withCurrent #[] frame beforeMachine
  let result : OpTy Provenance := ⟨.immediate (.scalar (.fromBool value)),RootCompilerFacts.boolLayout⟩
  have read : control.returnOperand () before = (before,.ok result) :=
    PrimitiveCallReturn.read_current_return options limits (remaining+1) span #[] frame beforeMachine
      RootCompilerFacts.boolLayout (.scalar (.fromBool value)) valid0 live0 cached0 (by decide +kernel)
      noLocalClocks beforeGhost
  have pop : control.popFrame () before = (state,.ok frame) := by
    rw [stateEq]
    exact ActualPopPlan.pop_of_plan options limits (remaining+1) span #[] frame beforeMachine beforeTracker borrowFrame
      beforeTracked frameTracked releasedMemory (RootPhysicalReturnPlan.to_plan plan) thread active
  obtain ⟨updated, copied, tree, bytes, len, mask, prov, encoding, mutability⟩ :=
    PhysicalBoolReturn.copy_return context validationContext options remaining span accessEq validationWidth validationRuntimeSize
      sameRuntime limits fuel debugOff validationFuel state place id root child written base count entry tracker value one layout width
      positive signedFits cached present size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend
      enabled extras rootFree childFree initialTree pointer aligned runtimeSize outerAccessEq ghost shallow
      frame.returnPlace destination finish endpoint
  let after := CanonicalCopy.replaceAllocation state id entry.kind updated
  have cleanup := RootPhysicalReturnSupport.cleanup_actual_stop options limits (remaining+1) span after frame continuation immediateLocals varargs
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [sourceBody]; simp [block]
  have normal : block.cleanup = false := by with_unfolding_all rfl
  have empty : after.stack.frames = #[] := by rw [show after.stack.frames = state.stack.frames from rfl,stateEq]
  have returned := RootPhysicalReturnSupport.normal_stop control () before before state after frame ⟨10,0⟩ block result
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt normal read pop copied cleanup continuation empty
  exact ⟨updated,returned,tree,bytes,len,mask,prov,encoding,mutability⟩

theorem return_step (context validationContext : Context)
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
    (accountedEq : beforeMachine = (SourceControl.accounted
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators
      (Storage.withCurrent #[] frame initialMachine)).machine)
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
    (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (noLocalClocks : frame.extra.dataRace = none)
    (beforeGhost : beforeMachine.user.payload.ghost = false)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (value : Bool)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
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
    ∃ updated, ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame initialMachine) =
      ({state with machine := {state.machine with memory :=
        {state.machine.memory with live := ((state.machine.memory.live.filter fun (row : AllocId × LocalAllocation Provenance BorrowTree MiriMemoryKind) => row.1 != id).push
          (id,{entry with allocation := updated}))}}},.ok true) ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  obtain ⟨updated, returned, tree, bytes, len, mask, prov, encoding, mutability⟩ :=
    driver context validationContext options remaining span accessEq validationWidth validationRuntimeSize sameRuntime limits fuel debugOff validationFuel frame beforeMachine beforeTracker borrowFrame beforeTracked frameTracked releasedMemory plan thread active state stateEq sourceBody location valid0 noLocalClocks beforeGhost continuation immediateLocals varargs place id root child written base count entry tracker value live0 cached0 one layout width positive signedFits cached present size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend enabled extras rootFree childFree initialTree pointer aligned runtimeSize outerAccessEq ghost shallow destination finish endpoint
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] frame initialMachine
  let accounted := Storage.withCurrent #[] frame beforeMachine
  have accounting := SourceControl.before_terminator config limits () initial
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks config limits).beforeTerminator () initial = (accounted,.ok ()) := by
    dsimp only [accounted]
    rw [accountedEq]
    exact accounting
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[0]? = none := by with_unfolding_all rfl
  have kind : block.terminator.kind = .Return := by with_unfolding_all rfl
  refine ⟨updated, ?_,tree,bytes,len,mask,prov,encoding,mutability⟩
  exact GenericCallReturn.return_step_exact config limits () initial accounted _ frame ⟨10,0⟩ block
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement kind accounting' returned

theorem terminal_empty
    (config : ExecutionMachine.Config K U C O X Host) (limits : ExecutionMachine.Limits)
    [DecidableEq K] (choice : C) (machine : MachineHooks.MachineState K U) :
    ExecutionMachine.step config limits choice ⟨⟨#[]⟩,machine⟩ = (⟨⟨#[]⟩,machine⟩,.ok false) := by
  rfl

theorem return_step_terminal (context validationContext : Context)
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
    (accountedEq : beforeMachine = (SourceControl.accounted
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators
      (Storage.withCurrent #[] frame initialMachine)).machine)
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
    (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (noLocalClocks : frame.extra.dataRace = none)
    (beforeGhost : beforeMachine.user.payload.ghost = false)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (place : MPlaceTy Provenance) (id : AllocId) (root child : BorTag) (written : Bool) (base count : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tracker : MachineHooks.BorrowState)
    (value : Bool)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (one : count = 1)
    (layout : place.layout = RootCompilerFacts.boolLayout)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
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
    ∃ updated, ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame initialMachine) =
      (CanonicalCopy.replaceAllocation state id entry.kind updated,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (CanonicalCopy.replaceAllocation state id entry.kind updated) =
        (CanonicalCopy.replaceAllocation state id entry.kind updated,.ok false) ∧
      updated.extra = parentWrittenTree root child count ∧ updated.byteSize = entry.allocation.byteSize ∧ updated.len = entry.allocation.len ∧
      updated.initializationMask = InitMask.new entry.allocation.byteSize true ∧
      updated.provenanceMap = ProvenanceMap.new ∧ target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) = .ok (AllocationCopy.snapshot updated) ∧
      updated.mutability = entry.allocation.mutability := by
  obtain ⟨updated, stepped, tree, bytes, len, mask, prov, encoding, mutability⟩ :=
    return_step context validationContext options remaining span accessEq validationWidth validationRuntimeSize sameRuntime limits fuel debugOff validationFuel frame initialMachine beforeMachine accountedEq unchecked noGc fixed beforeTracker borrowFrame beforeTracked frameTracked releasedMemory plan thread active state stateEq sourceBody location valid0 noLocalClocks beforeGhost continuation immediateLocals varargs place id root child written base count entry tracker value live0 cached0 one layout width positive signedFits cached present size mutable maskValid runtimeWidth storage maskLength provenance noClocks noBackend enabled extras rootFree childFree initialTree pointer aligned runtimeSize outerAccessEq ghost shallow destination finish endpoint
  have terminal : ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (CanonicalCopy.replaceAllocation state id entry.kind updated) =
      (CanonicalCopy.replaceAllocation state id entry.kind updated,.ok false) := by
    rw [stateEq]
    exact terminal_empty _ limits () _
  exact ⟨updated,stepped,terminal,tree,bytes,len,mask,prov,encoding,mutability⟩

#print axioms return_step_terminal

#print axioms return_step
#print axioms terminal_empty

#print axioms driver
end DuplicatePrefix.RootPhysicalReturn
open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RootPhysicalReturn.driver,
      ``DuplicatePrefix.RootPhysicalReturn.return_step, ``DuplicatePrefix.RootPhysicalReturn.return_step_terminal, ``DuplicatePrefix.RootPhysicalReturn.terminal_empty] do
   for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved root physical return dependency {dependency}"
