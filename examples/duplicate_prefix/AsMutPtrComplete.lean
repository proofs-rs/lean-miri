import duplicate_prefix.AsMutPtrBody
import duplicate_prefix.AsMutPtrReturn
import duplicate_prefix.AsMutPtrRelease
import duplicate_prefix.PointerAddComplete
namespace DuplicatePrefix.AsMutPtrComplete
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem body_and_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (carrierValid : AsMutPtrCarrier.Valid machine (.inl pointer) len)
    (size : frame.locals.size = 5)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl pointer)
        (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some ActualReferenceMetadata.reference)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).entries.any (·.value.ty == 4) = false)
    (callerId : Miri.MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerLive : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerCached : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (varargs : frame.vaList = #[])
    (borrowFrame : Miri.TreeBorrows.FrameState)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (finalMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {AsMutPtrReturn.writeFrame caller callerId (.scalar (Scalar.fromPointer config.access.runtime.base pointer)) callerValid with location := .mir ⟨target,0⟩}
          (AsMutPtrReturn.poppedMachine frames caller done
            (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span machine) finalMemory tracker borrowFrame)
            (thread.topUserRelevantFrame.getD (frames.push caller).size))) ∧ done.extra = frame.extra := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let value : Scalar Provenance := Scalar.fromPointer config.access.runtime.base pointer
  obtain ⟨done,trace,doneBody,doneIdentity,doneFn,doneExtra,doneReturn,doneCont,doneVa,doneLocalsIdentity,
    doneArg1,doneSize,doneLocation,done0,done2,done3,done4⟩ := AsMutPtrBody.actual_ten_statements
      options limits remaining span debugOff fuel validationFuel (frames.push caller) frame machine pointer len carrierValid
      size live0 uncached0 live1 cached1 dead2 uncached2 dead3 uncached3 dead4 uncached4 body identity callee location
      noClocks tracker tracked defaultMode ghost shallow dynamicFuel dynamicEq cmp metadata notConstructed
  have valid0 : (0 : Miri.MIR.LocalId) < done.locals.size := by rw [doneSize];decide
  have valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have slot0 : done.locals[0] = ⟨.live (.immediate (.scalar value)),some CopyCompilerFacts.destPointerLayout⟩ := by
    simpa only [Array.getElem?_eq_getElem valid0,Option.some.injEq] using done0
  have direct := PointerAddComplete.all_direct_five done.locals doneSize
    (by simp [done0,PointerAddComplete.isDirect])
    (by rw [doneArg1,Array.getElem?_eq_getElem valid1];simp [live1,PointerAddComplete.isDirect])
    (by simpa only [Option.map_map,Function.comp_def,Option.map_some,PointerAddComplete.isDirect] using congrArg (Option.map PointerAddComplete.isDirect) done2)
    (by simpa only [Option.map_map,Function.comp_def,Option.map_some,PointerAddComplete.isDirect] using congrArg (Option.map PointerAddComplete.isDirect) done3)
    (by simpa only [Option.map_map,Function.comp_def,Option.map_some,PointerAddComplete.isDirect] using congrArg (Option.map PointerAddComplete.isDirect) done4)
  have returned := AsMutPtrReturn.return_step options limits remaining span debugOff fuel validationFuel
    frames caller done machine value callerId (by rw [doneBody];exact body) doneLocation valid0
    (by rw [slot0]) (by rw [slot0]) (by rw [doneExtra];exact noClocks)
    callerValid callerLive callerCached callerClocks (by rw [doneReturn];exact destination) target unwindAction
    (by rw [doneCont];exact continuation) direct (by rw [doneVa];exact varargs) tracker borrowFrame tracked
    (by rw [doneExtra];exact frameTracked) finalMemory plan thread active unchecked noGc fixed ghost shallow
  exact ⟨done,SuccessfulTrace.append trace (.next returned (.refl _)),doneExtra⟩

theorem source_shaped_body_and_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (carrierValid : AsMutPtrCarrier.Valid machine (.inl pointer) len)
    (size : frame.locals.size = 5)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl pointer)
        (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some ActualReferenceMetadata.reference)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame machine)).entries.any (·.value.ty == 4) = false)
    (callerId : Miri.MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerLive : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerCached : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (varargs : frame.vaList = #[])
    (borrowFrame : Miri.TreeBorrows.FrameState)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (mask : ProtectedBorrowAccess.SixMask tags tracker.global.protectedTags true)
    (capacity offset finish : UInt64)
    (owned : borrowFrame.protectedTags = #[(id,tags 5)])
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : entry.allocation.extra = NestedBorrowAccess.nestedTree tags
      (BorrowRangeAccess.partitionWithInside capacity offset finish BorrowRangeAccess.rootLocation
        (NestedBorrowAccess.nestedLocation false)))
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {AsMutPtrReturn.writeFrame caller callerId (.scalar (Scalar.fromPointer config.access.runtime.base pointer)) callerValid with location := .mir ⟨target,0⟩}
          (AsMutPtrReturn.poppedMachine frames caller done
            (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span machine) (StackPopRelease.commitTree machine.memory id entry entry.allocation.extra) tracker borrowFrame)
            (thread.topUserRelevantFrame.getD (frames.push caller).size))) ∧ done.extra = frame.extra := by
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory
      (StackPopRelease.commitTree machine.memory id entry entry.allocation.extra) := by
    rw [owned]
    exact AsMutPtrRelease.buffer_plan machine.memory id entry tags tracker.global.protectedTags mask distinct
      capacity offset finish present tree
  exact body_and_return options limits remaining span debugOff fuel validationFuel frames caller frame machine pointer len carrierValid
    size live0 uncached0 live1 cached1 dead2 uncached2 dead3 uncached3 dead4 uncached4 body identity callee location
    noClocks tracker tracked defaultMode ghost shallow dynamicFuel dynamicEq cmp metadata notConstructed
    callerId callerValid callerLive callerCached callerClocks destination target unwindAction continuation varargs borrowFrame frameTracked
    (StackPopRelease.commitTree machine.memory id entry entry.allocation.extra) plan thread active unchecked noGc fixed

#print axioms source_shaped_body_and_return

#print axioms body_and_return
end
end DuplicatePrefix.AsMutPtrComplete
