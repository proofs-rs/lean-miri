import duplicate_prefix.AsMutInitializedShape
import duplicate_prefix.AsMutPtrComplete
import duplicate_prefix.GeneralBorrowExposedScopedAsMutEntry
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutInitializedComplete
variable [area : GeneralBorrowExposedKnownRootState.Scope]
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem run
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (debugOff : options.place.debugAssertions = false)
    (fuel : Nat) (validationFuel : options.limits.validation = fuel+1)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (initial : RootState) (initialNoRace : initial.machine.dataRace = none)
    (parent : Immediate Provenance)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tag : BorTag)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (releaseData : GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan.Input entry.allocation.extra tracker.global.protectedTags tag)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (callerId : MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerLive : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerCached : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    let pointer := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
    let adjusted := (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base
      pointer len ActualReferenceMetadata.reference).imm
    let destination := (LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout).stackView
    let frame := GeneralBorrowExposedScopedAsMutEntry.initialized options initial destination parent adjusted id tag
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace config limits (Storage.withCurrent (frames.push caller) frame machine)
        (Storage.withCurrent frames
          {AsMutPtrReturn.writeFrame caller callerId (.scalar (Scalar.fromPointer config.access.runtime.base pointer)) callerValid with location := .mir ⟨7,0⟩}
          (AsMutPtrReturn.poppedMachine frames caller done
            (ActualPopPlan.released (AsMutPtrReturn.accountedMachine options remaining span machine)
              (StackPopRelease.commitTree machine.memory id entry (GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan.release entry.allocation.extra tracker.global.protectedTags tag).tree) tracker (({} : FrameState).addProtector id tag))
            (thread.topUserRelevantFrame.getD (frames.push caller).size))) ∧ done.extra = frame.extra := by
  let pointer : Pointer Provenance := Pointer.new (.concrete id tag) (Size.ofBytes (base+offset))
  let adjusted := (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len ActualReferenceMetadata.reference).imm
  let destination := (LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout).stackView
  let frame := GeneralBorrowExposedScopedAsMutEntry.initialized options initial destination parent adjusted id tag
  have slots := AsMutInitializedShape.locals options initial destination parent adjusted id tag
  have size : frame.locals.size = 5 := by rw [show frame.locals = _ from slots];rfl
  have frameFacts := AsMutInitializedShape.fixed options initial destination parent adjusted id tag
  have frameRace : frame.extra.dataRace = none := by
    change ((AsMutPush.fresh initial.machine).1.dataRace.map _) = none
    change initial.machine.dataRace.map _ = none
    rw [initialNoRace];rfl
  have carrier : AsMutPtrCarrier.Valid machine (.inl pointer) len :=
    .positive id tag base offset len entry cachedAddress present positive nonzero signedFits
      bounds
  apply AsMutPtrComplete.body_and_return options limits remaining span debugOff fuel validationFuel
    frames caller frame machine pointer len carrier size
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    (by simp only [show frame.locals = _ from slots];rfl)
    frameFacts.1 frameFacts.2.1 frameFacts.2.2.1 frameFacts.2.2.2.1 frameRace
    tracker tracked defaultMode ghost shallow dynamicFuel dynamicEq cmp metadata notConstructed
    callerId callerValid callerLive callerCached callerClocks (by rfl) 7 .Continue (by rfl) (by rfl)
    (({} : FrameState).addProtector id tag) (by rfl)
    (StackPopRelease.commitTree machine.memory id entry (GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan.release entry.allocation.extra tracker.global.protectedTags tag).tree)
    (by exact GeneralBorrowExposedScopedInactiveWritableAsMutReleasePlan.to_plan machine.memory tracker.global.protectedTags id tag entry present releaseData)
    thread active unchecked noGc fixed

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``run) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved initialized asmut complete dependency {dependency}"
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableAsMutInitializedComplete
