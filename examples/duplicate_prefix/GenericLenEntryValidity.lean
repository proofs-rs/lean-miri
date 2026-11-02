import duplicate_prefix.ProtectedReferenceValidator
import duplicate_prefix.GeneralBorrowFreshSharedNext
import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.ProtectedStages
namespace DuplicatePrefix.GenericLenEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem positive_data
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
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
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset)))
      len SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let finalTree := (GeneralBorrowFreshSharedSequence.child
      second tracker.global.protectedTags true).tree
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag) with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  have info := RootReferenceInfo.facts options remaining span ctx true
  have successes := GeneralBorrowFreshSharedSequence.two initialTree tracker.global.protectedTags target exprTag
    tracker.global.nextPointerTag offset len first second owned
  let parentTree := (GeneralBorrowFreshSharedSequence.read second tracker.global.protectedTags true).tree
  let finalTree := (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree
  have physicalBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [←allocationSize,tree]
    exact second.bounds
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree = parentTree := by
    rw [tree]
    dsimp only [parentTree,GeneralBorrowFreshSharedSequence.read,GeneralBorrowFreshSharedSequence.registered]
    rw [secondParent]
    rfl
  have readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete exprTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).status = .Completed := by
    rw [tree]
    simpa only [GeneralBorrowFreshSharedSequence.read,GeneralBorrowFreshSharedSequence.registered,secondParent,ite_true,TypedBorrowSteps.registeredGlobal] using successes.2.2.1
  have child : parentTree.newChild (Size.ofBytes offset) (.concrete exprTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) frozenRead) (sharedPolicy true).outsidePermission true =
        ⟨finalTree,.ok ()⟩ := by
    rw [←secondParent]
    have succeeded := successes.2.2.2.1
    change (GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).outcome = .ok () at succeeded
    change GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true =
      ⟨(GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true).tree,.ok ()⟩
    cases childEq : GeneralBorrowFreshSharedSequence.child second tracker.global.protectedTags true with
    | mk treeResult result =>
      simp only [childEq] at succeeded
      cases succeeded
      rfl
  have result := ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
    rfl (by decide +kernel) (shared_initial true) shared_entry_policy
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&[u8]" info.named info.classified
    id entry base offset len exprTag positive nonzero signedFits physicalBounds frames frame machine tracker enabled mode
    borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress present race parentTree finalTree
    readTree readDone child metadata notConstructed
  exact result



theorem positive
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
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
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset)))
      len SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let finalTree := (GeneralBorrowFreshSharedSequence.child
      (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
        offset len first noFree room freshTag freshProtector different cleanFuture owned).val tracker.global.protectedTags true).tree
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag) with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  exact positive_data options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq id entry base offset len initialTree target exprTag positive nonzero signedFits frames frame machine tracker enabled mode borrowFrame frameBorrow fresh first (GeneralBorrowFreshSharedNext.next initialTree tracker.global.protectedTags target exprTag tracker.global.nextPointerTag
      offset len first noFree room freshTag freshProtector different cleanFuture owned).val rfl owned tree allocationSize localId valid live cached ghost shallow cachedAddress present race metadata notConstructed

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved entry validity dependency {dependency}"
end
end DuplicatePrefix.GenericLenEntryValidity
