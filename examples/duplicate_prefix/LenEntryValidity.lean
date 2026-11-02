import duplicate_prefix.ProtectedReferenceValidator
import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.ProtectedStages
namespace DuplicatePrefix.LenEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem positive
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree3 tags
      (partitionWithInside capacity offset (offset+len) rootLocation (location3 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 3 false)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset)))
      len SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let finalTree := tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 false))
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
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  have registeredMask : ProtectedStages.StageMask tags registered.protectedTags 3 false := by
    intro index inside
    have indexNot3 : index ≠ 3 := by intro same;subst index;change (3 : Nat) < 3 at inside;omega
    have different : tags index ≠ tags 3 := fun same => indexNot3 (distinct same)
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains (tags index) = _
    rw [nextTag,ProtectorInsertion.contains_other _ _ _ _ different]
    exact mask index inside
  have parentRead := ProtectedStages.parent_read3 tags distinct registered.protectedTags registeredMask
    capacity offset len false positive bounds
  have constructed := NestedConstruction.new_shared_entry3 tags distinct capacity offset len positive bounds
  have physicalBounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    simpa only [allocationSize,Size.ofBytes] using bounds
  let parentTree := tree3 tags (partitionWithInside capacity offset (offset+len) rootLocation (location3 true))
  let finalTree := tree4 tags (partitionWithInside capacity offset (offset+len) rootLocation (location4 false))
  have result := ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
    rfl (by decide +kernel) (shared_initial true) shared_entry_policy
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&[u8]" info.named info.classified
    id entry base offset len (tags 2) positive nonzero signedFits physicalBounds frames frame machine tracker enabled mode
    borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress present race parentTree finalTree
    (by rw [tree];exact parentRead.2) (by rw [tree];exact parentRead.1)
    (by simpa only [nextTag,sharedPolicy,Option.isSome_some,↓reduceIte] using constructed) metadata notConstructed
  exact result

#print axioms positive
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``positive) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved entry validity dependency {dependency}"
end
end DuplicatePrefix.LenEntryValidity
