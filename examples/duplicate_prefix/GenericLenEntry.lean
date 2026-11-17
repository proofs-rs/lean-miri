import duplicate_prefix.LenEntry
import duplicate_prefix.GenericLenInstall
namespace DuplicatePrefix.GenericLenEntry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem actual_entry_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (first : GeneralBorrowFreshSharedSequence.Data initialTree exprTag target offset len)
    (second : GeneralBorrowFreshSharedSequence.Data
      (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree
      tracker.global.nextPointerTag (GeneralBorrowFreshSharedSequence.index first) offset len)
    (secondParent : second.parentTag = exprTag)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned initialTree tracker.global.protectedTags target .Write) offset (offset+len) initialTree.locations)
    (tree : entry.allocation.extra = (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := (GeneralBorrowFreshSharedSequence.child
      second tracker.global.protectedTags true).tree
    let afterFrame := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame frameValid output) {} id tracker.global.nextPointerTag
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  let cfg := config options remaining span
  let state := Storage.withCurrent frames caller machine
  let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
  let frame := LenEntry.rawFrame options state destination
  let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
  have size : frame.locals.size = 3 := LenEntry.raw_size options state destination
  have valid1 : 1 < frame.locals.size := by rw [size];decide
  have postTracked : postMachine.borrowTracker = some tracker := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact enabled
  have postGhost : postMachine.user.payload.ghost = false := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact ghost
  have postShallow : postMachine.user.payload.validation = .Shallow := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact shallow
  have postAddress : postMachine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩ := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact cachedAddress
  have postPresent : postMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry) := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact present
  have postRace : postMachine.dataRace = none := by
    simp only [postMachine,LenPush.completed,LenPush.fresh,CallEntryFacts.freshRoot,Storage.withCurrent,
      GenericPushRelevance.afterPush]
    split <;> exact race
  have frameBorrow : frame.extra.borrowTracker = some {} := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,enabled]
  have frameRace : frame.extra.dataRace = none := by
    simp [frame,LenEntry.rawFrame,LenFrame.rawFrame,LenPush.fresh,CallEntryFacts.freshRoot,state,Storage.withCurrent,race]
  have made := GenericLenInstall.scoped_install_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len initialTree target exprTag positive nonzero signedFits (frames.push caller) frame postMachine
    tracker postTracked {} frameBorrow fresh first second secondParent owned tree allocationSize valid1 rfl rfl rfl rfl rfl frameRace postGhost postShallow
    postAddress postPresent postRace metadata notConstructed
  let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let af := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid1 output) {} id tracker.global.nextPointerTag
  have afSize : af.locals.size = 3 := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,Array.size_set] using size
  have afValid : 0 < af.locals.size := by rw [afSize];decide
  have afDead : af.locals[0].value = .dead := by
    simp [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,
      LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
      Array.getElem_set,frame,LenEntry.rawFrame,LenFrame.rawFrame,Frame.create]
  have afRace : af.extra.dataRace = none := by
    simpa only [af,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,LenInstall.resultFrame,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame] using frameRace
  exact LenEntry.actual_entry_of_install options limits remaining span debugOff frames caller machine tracker enabled _
    localId valid old live cached noClocks race ghost shallow thread index current active top presentFrame _ _ made
    rfl rfl rfl afValid afDead afRace


theorem actual_entry
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (first : GeneralBorrowFreshSharedSequence.Data initialTree exprTag target offset len)
    (noFree : initialTree.tagMapping.deassigned.back? = none)
    (room : initialTree.tagMapping.mapping.size+1 ≤ 4294967295)
    (freshTag : GeneralBorrowTagMap.Fresh initialTree.tagMapping tracker.global.nextPointerTag)
    (freshProtector : GeneralBorrowProtector.Fresh initialTree tracker.global.nextPointerTag)
    (different : exprTag ≠ tracker.global.nextPointerTag)
    (cleanFuture : GeneralRangeMapState.Every
      (fun location : LocationTree => location.perms.get (GeneralBorrowFreshSharedNext.future initialTree) = none) initialTree.locations)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowRange.LocationOwned initialTree tracker.global.protectedTags target .Write) offset (offset+len) initialTree.locations)
    (tree : entry.allocation.extra = (GeneralBorrowFreshSharedSequence.child first tracker.global.protectedTags false).tree)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < caller.locals.size) (old : Immediate Provenance)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (thread : Miri.Concurrency.ThreadRecord) (index : Nat) (current : CompilerFrameContext.ActualFrame)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack thread.topUserRelevantFrame = some index)
    (presentFrame : (LenPush.pushed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView).stack.frames[index]? = some current)
    (metadata : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (LenPush.completed options.userRelevantCrates (Storage.withCurrent frames caller machine)
      (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView current)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let state := Storage.withCurrent frames caller machine
    let destination := (LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout).stackView
    let frame := LenEntry.rawFrame options state destination
    let postMachine := (LenPush.completed options.userRelevantCrates state destination current).machine
    let frameValid : 1 < frame.locals.size := by rw [LenEntry.raw_size]; decide
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := (GeneralBorrowFreshSharedSequence.child
      (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
        offset len first noFree room freshTag freshProtector different cleanFuture owned).val tracker.global.protectedTags true).tree
    let afterFrame := TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame frameValid output) {} id tracker.global.nextPointerTag
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine postMachine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory postMachine.memory id entry finalTree}
    Call.initStackFrame (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      LenHelper.resolved.callee LenHelper.body LenHelper.abi #[.Copy ⟨.immediate value,LenHelper.rawLayout⟩]
      false destination (.goto (some 3) .Continue) state =
      .ok () (Storage.withCurrent (frames.push caller)
        (LenDone.doneFrame {afterFrame with location := .unwinding LenEntryFacts.lenPreamble}) resultMachine) := by
  exact actual_entry_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len initialTree target exprTag positive nonzero signedFits frames caller machine tracker enabled fresh first (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
      offset len first noFree room freshTag freshProtector different cleanFuture owned).val rfl owned tree allocationSize localId valid old live cached noClocks ghost shallow cachedAddress present race thread index current active top presentFrame metadata notConstructed

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``actual_entry) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved len positive entry {dependency}"
end
end DuplicatePrefix.GenericLenEntry
