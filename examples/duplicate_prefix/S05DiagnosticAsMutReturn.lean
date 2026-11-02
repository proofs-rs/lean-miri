import duplicate_prefix.S05DiagnosticAsMutRelease
import duplicate_prefix.GenericAsMutReturnState
namespace DuplicatePrefix.S05DiagnosticAsMutReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Physical as_mut_ptr Return to the reflected call's actual target block7.
The exact release is derived internally, and the entire post-machine is exposed. -/
theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (base : UInt64)
    (sourceBody : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (location : frame.location = .mir ⟨0,10⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 13)) (Size.ofBytes base))))))
    (cached0 : frame.locals[0].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (callerValid : (15 : MIR.LocalId) < caller.locals.size)
    (callerLive : caller.locals[15].value = .live (.immediate .uninit))
    (callerCached : caller.locals[15].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller 15 CopyCompilerFacts.destPointerLayout)
    (continuation : frame.returnContinuation = .goto (some 7) .Continue)
    (immediate : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (treeEq : entry.allocation.extra = (S05DiagnosticAsMutRead.afterRead.newChild Size.ZERO
      (.concrete (S05DiagnosticFnEntryRead.tag 12)) (S05DiagnosticFnEntryRead.tag 13)
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true).tree)
    (protectedEq : tracker.global.protectedTags = S05DiagnosticAsMutRelease.protections)
    (frameTracked : frame.extra.borrowTracker = some (({} : FrameState).addProtector id (S05DiagnosticFnEntryRead.tag 13)))
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let value : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
      (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 13)) (Size.ofBytes base))
    let borrowFrame := ({} : FrameState).addProtector id (S05DiagnosticFnEntryRead.tag 13)
    let finalMemory := StackPopRelease.commitTree machine.memory id entry S05DiagnosticAsMutRelease.released
    let post := GenericAsMutReturnState.machine options remaining span frames caller frame machine finalMemory tracker borrowFrame thread
    ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) frame machine) =
      (Storage.withCurrent frames {AsMutPtrReturn.writeFrame caller 15 (.scalar value) callerValid with location := .mir ⟨7,0⟩} post,.ok true) ∧
    post.memory = finalMemory ∧ post.borrowTracker = some {tracker with global := tracker.global.endCall borrowFrame} ∧
    post.user.addresses = machine.user.addresses ∧ post.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
    post.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras := by
  dsimp only
  let value : Scalar Provenance := Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
    (Pointer.new (.concrete id (S05DiagnosticFnEntryRead.tag 13)) (Size.ofBytes base))
  let borrowFrame := ({} : FrameState).addProtector id (S05DiagnosticFnEntryRead.tag 13)
  let finalMemory := StackPopRelease.commitTree machine.memory id entry S05DiagnosticAsMutRelease.released
  have complete : entry.allocation.extra.releaseProtector (S05DiagnosticFnEntryRead.tag 13) tracker.global.protectedTags =
      ⟨S05DiagnosticAsMutRelease.released,.Released⟩ := by
    rw [treeEq,protectedEq]
    exact S05DiagnosticAsMutRelease.actual_release
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList machine.memory finalMemory := by
    change StackPopRelease.Plan tracker.global.protectedTags [(id,S05DiagnosticFnEntryRead.tag 13)] machine.memory finalMemory
    exact .live id (S05DiagnosticFnEntryRead.tag 13) entry S05DiagnosticAsMutRelease.released [] machine.memory finalMemory present complete (.nil finalMemory)
  have returned := AsMutPtrReturn.return_step options limits remaining span debugOff fuel validationFuel frames caller frame machine value 15
    sourceBody location valid0 live0 cached0 noClocks callerValid callerLive callerCached callerClocks destination
    7 .Continue continuation immediate varargs tracker borrowFrame tracked frameTracked finalMemory plan thread active unchecked noGc fixed ghost shallow
  obtain ⟨memory,trackedAfter,_race,_fixed,addresses,_ghost,_shallow,types,_backend,extras⟩ :=
    GenericAsMutReturnState.fields options remaining span frames caller frame machine finalMemory tracker borrowFrame thread
  exact ⟨returned,memory,trackedAfter,addresses,types,extras⟩
end
end DuplicatePrefix.S05DiagnosticAsMutReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticAsMutReturn." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic as_mut_ptr return dependency {dependency}"
