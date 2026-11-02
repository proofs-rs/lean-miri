import duplicate_prefix.GeneralBorrowFreshRootScopedAsMutTail
import duplicate_prefix.AsMutPush
import duplicate_prefix.CallLocalRead
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedAsMutEntry
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def rawFrame (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :=
  let supply := AsMutPush.fresh state.machine
  AsMutFrame.rawFrame options.userRelevantCrates supply.1 destination supply.2

theorem raw_size (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance) :
    (rawFrame options state destination).locals.size = 5 := by with_unfolding_all rfl

def initialized (options : EvalConfigurationCore.Options) (state : RootState) (destination : RuntimeStackPlace Provenance)
    (value adjusted : Immediate Provenance) (id : AllocId) (tag : BorTag) :=
  AsMutDone.doneFrame {(GeneralBorrowFreshRootScopedAsMutInstall.resultFrame (rawFrame options state destination)
    (by rw [raw_size];decide) value adjusted {} id tag) with location := .unwinding AsMutEntryFacts.asMutPreamble}

theorem actual_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowFreshRootScopedFnEntry.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destId : MIR.LocalId) (destValid : destId < caller.locals.size) (old : Immediate Provenance)
    (destLive : caller.locals[destId].value = .live (.immediate old))
    (destCached : caller.locals[destId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (topPresent : (AsMutPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView).stack.frames[index]? = some current) :
    let cfg := config options remaining span
    let before := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let adjusted := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
    let finalTree := GeneralBorrowFreshRootScopedFnEntryArgument.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody HelperCompilerFacts.asMutPtrAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩] false destination (.goto (some 7) .Continue) before =
      .ok () (Storage.withCurrent (frames.push caller)
        (initialized options before destination value adjusted id tracker.global.nextPointerTag) resultMachine) := by
  let before := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller destId CopyCompilerFacts.destPointerLayout).stackView
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let frame := rawFrame options before destination
  let postMachine := (AsMutPush.completed options.userRelevantCrates before destination current).machine
  have read := CallLocalRead.place_to_op_cached options limits (remaining+1) span debugOff frames caller machine destId
    CopyCompilerFacts.destPointerLayout old destValid destLive destCached (by decide +kernel) callerClocks ghost
  have pushed := AsMutPush.actual_push options () (remaining+1) span before destination thread index current active top topPresent
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact enabled
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact shallow
  have postCached : postMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have postPresent : postMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact present
  have postRace : postMachine.dataRace = none := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact race
  have postMetadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame postMachine)).metadata = PreparedReflection.actual.runtime := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact metadata
  have postConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent (frames.push caller) frame postMachine)).entries.any (·.value.ty == 4) = false := by
    simp only [postMachine,AsMutPush.completed,AsMutPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,GenericPushRelevance.afterPush]
    split <;> exact notConstructed
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,race]
  have frameBorrow : frame.extra.borrowTracker = some ({} : FrameState) := by
    simp [frame,rawFrame,AsMutFrame.rawFrame,AsMutPush.fresh,CallEntryFacts.freshRoot,before,Storage.withCurrent,enabled]
  have frameSize : frame.locals.size = 5 := raw_size options before destination
  have tail := GeneralBorrowFreshRootScopedAsMutTail.run options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds
    (frames.push caller) frame postMachine tracker postTracked defaultMode {} frameBorrow fresh runtime raw rawTag rawOffset rawLen capacity
    (by rw [frameSize];decide) rfl rfl rfl (by with_unfolding_all rfl) (by with_unfolding_all rfl) frameRace
    postGhost postShallow postCached postPresent postRace postMetadata postConstructed old CopyCompilerFacts.destPointerLayout
    AsMutEntryFacts.asMutPreamble rfl rfl (by with_unfolding_all rfl)
  dsimp only
  rw [AsMutCallCore.actual_entry_eq,GeneralBorrowFreshRootScopedAsMutTail.core_eq]
  simp only [bind,EStateM.bind]
  rw [read]
  dsimp only
  have pushActual : h.pushRaw () HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before =
      .ok () (AsMutPush.completed options.userRelevantCrates before destination current) := by
    change CallMachine.pushRaw (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle
      (PreparedContracts.actualConfig options () (remaining+1) span).compiler.debugAssertions
      HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue) before = _
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).debug,debugOff]
    exact pushed
  dsimp only [h,before,destination] at pushActual
  rw [pushActual]
  exact tail

#print axioms actual_entry
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut entry dependency {dependency}"
end
end DuplicatePrefix.GeneralBorrowFreshRootScopedAsMutEntry
