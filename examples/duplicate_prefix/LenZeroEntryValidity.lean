import duplicate_prefix.ProtectedZeroReferenceValidator
import duplicate_prefix.EmptyBorrowHelpers
import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.ProtectorInsertion
import duplicate_prefix.ProtectedStages
namespace DuplicatePrefix.LenZeroEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem live_zero
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset : UInt64)
    (tree : entry.allocation.extra = tree3 tags
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset)))
      0 SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let finalTree := tree4 tags (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
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
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  have info := RootReferenceInfo.facts options remaining span ctx true
  let finalTree := tree4 tags (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes capacity) rootLocation)
  have result := ProtectedZeroReferenceValidator.live_zero options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
    rfl (by decide +kernel) (shared_initial true) shared_entry_policy
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&[u8]" info.named info.classified
    id entry base offset (tags 2) nonzero frames frame machine tracker enabled mode
    borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress present finalTree
    (by simpa only [tree,nextTag,finalTree,sharedPolicy,Option.isSome_some,↓reduceIte,Size.ZERO,Size.ofBytes] using EmptyBorrowHelpers.new_shared_entry3_zero tags distinct capacity offset) metadata notConstructed
  exact result

theorem nonlive_zero
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (allocation : AllocationInfo)
    (capacity base offset : UInt64)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (allocationInfo : machine.memory.getAllocInfo id = .ok allocation)
    (nonlive : allocation.kind ≠ .liveData)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (nextTag : tracker.global.nextPointerTag = tags 3)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id (tags 2)) (Size.ofBytes (base+offset)))
      0 SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let resultMachine := TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag) with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 SharedReferenceMetadata.sharedLayout).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  have info := RootReferenceInfo.facts options remaining span ctx true
  have result := ProtectedZeroReferenceValidator.nonlive_zero options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
    rfl (by decide +kernel) (shared_initial true) shared_entry_policy
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&[u8]" info.named info.classified
    id allocation base offset (tags 2) nonzero frames frame machine allocationInfo nonlive tracker enabled mode
    borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress metadata notConstructed
  exact result

theorem integer_zero
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let resultMachine := ReferenceBorrowDriver.allocatedMachine machine tracker fresh
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {frame with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.integerSliceValue address 0 SharedReferenceMetadata.sharedLayout).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  have info := RootReferenceInfo.facts options remaining span ctx true
  have result := ProtectedZeroReferenceValidator.integer_zero options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
    rfl (by decide +kernel) (shared_initial true) shared_entry_policy
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&[u8]" info.named info.classified
    address nonzero frames frame machine tracker enabled mode
    fresh localId valid live cached ghost shallow  metadata notConstructed
  exact result

#print axioms live_zero
open Lean Elab Command in
run_cmd do
  for declaration in [``live_zero, ``nonlive_zero, ``integer_zero] do
   for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved entry validity dependency {dependency}"
end
end DuplicatePrefix.LenZeroEntryValidity
