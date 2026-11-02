import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableArgumentRaw
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableMutableEntryConstructed
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableMutableArgumentReady
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
open GeneralBorrowExposedScopedWritableMutableArgumentRaw (copiedFrame)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual FnEntry argument copy retains the mixed writable-leaf contract on
its exact protected child; all retag/Read/constructor outcomes are derived. -/
theorem copy_argument_ready
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (selected head : UniIndex) (tail : List UniIndex)
    (data : GeneralBorrowExposedScopedWritableMutableEntryRaw.Data entry.allocation.extra tracker.global.protectedTags
      parentTag tracker.global.nextPointerTag offset len selected head tail)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,ActualReferenceMetadata.reference⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm),
             layout := (copied.locals[localId]'(by simpa only [copied,copiedFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,copiedFrame,Array.size_set] using valid)} resultMachine) ∧
    ∃ _context : GeneralBorrowExposedKnownRootRangeData.Context finalTree
      (GeneralBorrowFreshMetadataChildMutable.index data.input) selected head tail,
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty (GeneralBorrowExposedScopedWritableReadData.Data finalTree location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
        (GeneralBorrowFreshMetadataChildMutable.index data.input) selected head tail
        (fun position=>data.resources.component.support position ∨position=(GeneralBorrowFreshMetadataChildMutable.index data.input).toNat)
        (fun _=>true))) offset (offset+len) finalTree.locations := by
  constructor
  · exact GeneralBorrowExposedScopedWritableMutableArgumentRaw.copy_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds frames frame machine tracker enabled mode
      borrowFrame frameBorrow fresh selected head tail data capacity localId valid old live cached noClocks ghost shallow cachedAddress
      present race metadata notConstructed view destination
  · obtain ⟨readDone,childDone,context,owned⟩:=GeneralBorrowExposedScopedWindowWritableMutableEntryConstructed.run entry.allocation.extra
      tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail data
    dsimp only [GeneralBorrowExposedScopedWritableMutableArgumentRaw.finalTree,TypedBorrowSteps.registeredGlobal]
    exact ⟨context,owned⟩
end
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritableMutableArgumentReady
