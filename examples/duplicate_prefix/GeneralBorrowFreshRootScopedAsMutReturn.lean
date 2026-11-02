import duplicate_prefix.GeneralBorrowFreshRootScopedBothReleaseEndCall
import duplicate_prefix.GeneralBorrowFreshRootScopedFnEntryHidden
import duplicate_prefix.AsMutPtrReturn
import duplicate_prefix.GenericAsMutReturnState
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedAsMutReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- Actual helper Return from current raw mutable resources. The singleton
release plan and endCall successor capabilities are proved internally. -/
theorem from_current
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (value : Scalar Provenance) (callerId : Miri.MIR.LocalId)
    (sourceBody : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (location : frame.location = .mir ⟨0,10⟩)
    (valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar value)))
    (cached0 : frame.locals[0].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerValid0 : callerId < caller.locals.size)
    (callerLive0 : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerCached0 : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some tracker)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (pointerValue : value = Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))))
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (allocationPresent : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (anchor selected : UniIndex) (maximum : BorTag)
    (positive : GeneralBorrowFreshRootScopedRow.Positive entry.allocation.extra tracker.global.protectedTags
      anchor selected maximum offset len)
    (node : TreeNode) (nodePresent : entry.allocation.extra.nodeAt anchor = some node)
    (sameTag : node.tag = tag) (hidden : node.isExposed = false)
    (tagged : entry.allocation.extra.indexOfTag tag = some anchor)
    (distinct : entry.allocation.extra.roots.toList.Nodup)
    (short : entry.allocation.extra.nodes.size < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra anchor .Write offset (offset+len))
    (frameTracked : frame.extra.borrowTracker = some (({} : FrameState).addProtector id tag))
    (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let released := entry.allocation.extra.releaseProtector tag tracker.global.protectedTags
    let borrowFrame := ({} : FrameState).addProtector id tag
    let finalMemory := StackPopRelease.commitTree machine.memory id entry released.tree
    let finalMachine := GenericAsMutReturnState.machine options remaining span frames caller frame machine finalMemory tracker borrowFrame thread
    ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames
        {AsMutPtrReturn.writeFrame caller callerId (.scalar value) callerValid0 with location := .mir ⟨target,0⟩} finalMachine,.ok true) ∧
    finalMachine.memory = finalMemory ∧ finalMachine.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} ∧
    DuplicatePrefixBorrowContract.RuntimeFacts released.tree (tracker.global.endCall borrowFrame) ∧
    Nonempty (GeneralBorrowFreshRootScopedRow.Positive released.tree (tracker.global.endCall borrowFrame).protectedTags
      anchor selected maximum offset len) ∧
    released.tree.indexOfTag tag = some anchor ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin released.tree anchor .Write offset (offset+len) ∧
    finalMachine.user.addresses = machine.user.addresses ∧
    finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
    finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  let released := entry.allocation.extra.releaseProtector tag tracker.global.protectedTags
  let borrowFrame := ({} : FrameState).addProtector id tag
  let finalMemory := StackPopRelease.commitTree machine.memory id entry released.tree
  obtain ⟨releasedDone,afterRuntime,afterPositive,afterActivity,absent,other,shape,capacity⟩ :=
    GeneralBorrowFreshRootScopedBothReleaseEndCall.release_end_call entry.allocation.extra tracker.global runtime id tag anchor selected maximum offset len
      positive node nodePresent sameTag hidden tagged distinct short activity
  have releaseExact : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags = ⟨released.tree,.Released⟩ := by
    cases equation : entry.allocation.extra.releaseProtector tag tracker.global.protectedTags with
    | mk tree status =>
      simp only [equation] at releasedDone
      cases releasedDone
      unfold released
      rw [equation]
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory := by
    change StackPopRelease.Plan tracker.global.protectedTags [(id,tag)] machine.memory finalMemory
    exact .live id tag entry released.tree [] machine.memory finalMemory allocationPresent releaseExact (.nil finalMemory)
  have step := AsMutPtrReturn.return_step options limits remaining span debugOff fuel validationFuel frames caller frame machine value callerId
    sourceBody location valid0 live0 cached0 noClocks callerValid0 callerLive0 callerCached0 callerClocks destination
    target unwindAction continuation immediateLocals varargs tracker borrowFrame tracked frameTracked finalMemory plan thread active unchecked noGc fixed ghost shallow
  obtain ⟨memory,trackedAfter,race,fixedAfter,addresses,ghostAfter,shallowAfter,types,backend,extras⟩ :=
    GenericAsMutReturnState.fields options remaining span frames caller frame machine finalMemory tracker borrowFrame thread
  have taggedAfter : released.tree.indexOfTag tag = some anchor := by
    have mapping := congrArg BorrowTree.tagMapping shape
    change released.tree.tagMapping.get tag = some anchor
    rw [mapping]
    exact tagged
  exact ⟨step,memory,trackedAfter,afterRuntime,afterPositive,taggedAfter,afterActivity,addresses,types,extras⟩
end
end DuplicatePrefix.GeneralBorrowFreshRootScopedAsMutReturn
