import duplicate_prefix.GenericLenEntryValidity
import duplicate_prefix.LenArgumentCopy
namespace DuplicatePrefix.GenericLenArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext LenArgumentCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
theorem copy_argument_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
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
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := (GeneralBorrowFreshSharedSequence.child
      second tracker.global.protectedTags true).tree
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,SharedReferenceMetadata.sharedLayout⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),
             layout := (copied.locals[localId]'(by simpa only [copied,copiedFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,copiedFrame,Array.size_set] using valid)} resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let copied := copiedFrame frame localId value valid
  have postValid : localId < copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  have postLive : copied.locals[localId].value = .live (.immediate value) := by simp [copied,copiedFrame]
  have postCached : copied.locals[localId].layout = some SharedReferenceMetadata.sharedLayout := by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  have checked := GenericLenEntryValidity.positive_data options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    id entry base offset len initialTree target exprTag positive nonzero signedFits frames copied machine
    tracker enabled mode borrowFrame frameBorrow fresh first second secondParent owned
    tree allocationSize localId postValid postLive postCached ghost shallow cachedAddress present race metadata notConstructed
  apply copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked


theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (initialTree : BorrowTree) (target : UniIndex) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
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
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := (GeneralBorrowFreshSharedSequence.child
      (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
        offset len first noFree room freshTag freshProtector different cleanFuture owned).val tracker.global.protectedTags true).tree
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,SharedReferenceMetadata.sharedLayout⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),
             layout := (copied.locals[localId]'(by simpa only [copied,copiedFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,copiedFrame,Array.size_set] using valid)} resultMachine) := by
  exact copy_argument_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len initialTree target exprTag positive nonzero signedFits frames frame machine tracker enabled mode borrowFrame frameBorrow fresh first (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
      offset len first noFree room freshTag freshProtector different cleanFuture owned).val rfl owned tree allocationSize localId valid old live cached noClocks ghost shallow cachedAddress present race metadata notConstructed view destination

end
end DuplicatePrefix.GenericLenArgumentCopy
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.GenericLenArgumentCopy.copy_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved generic len argument dependency {dependency}"
