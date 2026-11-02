import duplicate_prefix.GeneralBorrowPositiveWildcardWindowRuntimeValidator
import duplicate_prefix.ReferenceArgumentCopy
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def copiedFrame (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId)
    (value : Immediate Provenance) (valid : localId < frame.locals.size) :=
  {frame with locals := (frame.locals.set localId
    {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}

def finalTree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (offset len : UInt64) :=
  let original := tree
  let tree := (tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed).tree
  let tag := tracker.global.nextPointerTag
  let index : UniIndex := ⟨UInt32.ofNat original.tagMapping.mapping.size⟩
  GeneralBorrowPositiveWildcardConstructor.result tree
    ⟨original.tagMapping.mapping.push (tag,index),original.tagMapping.deassigned⟩ index tag
    (.ReservedFrz false) .None ChildBorrow.fnEntryLocation offset len

/-- Actual MIR argument copy with real protected FnEntry runtime validation on
a general multiple-root forest. Every borrow success is derived from the
initial stable mutable Data; physical/compiler/fuel premises stay explicit. -/
theorem copy_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (pointerFits : base.toNat+offset.toNat+len.toNat<2^64)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (position : Nat) (positionValid : position < machine.user.addresses.intToPtrMap.size)
    (ordered : WildcardInteriorHitAddress.Ordered machine.user.addresses.intToPtrMap)
    (addressRow : machine.user.addresses.intToPtrMap[position]? = some ⟨base,id⟩)
    (beforeNext : ∀nextValid:position+1<machine.user.addresses.intToPtrMap.size,base+offset<machine.user.addresses.intToPtrMap[position+1].address)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (exposedAlloc : machine.user.addresses.exposed.contains id = true)
    (head : UniIndex) (extras : List UniIndex)
    (leafGeometry : GeneralBorrowSparseExposedLeafState.Geometry entry.allocation.extra head extras)
    (well : entry.allocation.extra.locations.WellFormed)
    (treeBounds : offset.toNat+len.toNat≤entry.allocation.extra.locations.size.bytes.toNat)
    (sourceRaw : GeneralRangeMapState.Every (fun location=>GeneralBorrowSparseExposedLeafState.Raw entry.allocation.extra location
      (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags) entry.allocation.extra.locations)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new .wildcard (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := GeneralBorrowPositiveWildcardWindowArgumentCopy.finalTree entry.allocation.extra tracker offset len
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
            (by simpa only [copied,copiedFrame,Array.size_set] using valid)} resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new .wildcard (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let copied := copiedFrame frame localId value valid
  have postValid : localId < copied.locals.size := by simpa only [copied,copiedFrame,Array.size_set] using valid
  have postLive : copied.locals[localId].value = .live (.immediate value) := by simp [copied,copiedFrame]
  have postCached : copied.locals[localId].layout = some ActualReferenceMetadata.reference := by
    simpa only [copied,copiedFrame,Array.getElem_set_self] using cached
  have info := RootReferenceInfo.facts options remaining span ctx false
  have checked := GeneralBorrowPositiveWildcardWindowRuntimeValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    ActualReferenceMetadata.reference info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&mut [u8]" info.named info.classified id entry base offset len positive nonzero signedFits bounds pointerFits frames copied machine
    tracker enabled mode borrowFrame frameBorrow fresh localId postValid postLive postCached ghost shallow cachedAddress present race
    position positionValid ordered addressRow beforeNext addressMode exposedAlloc head extras leafGeometry well treeBounds sourceRaw tagFresh noFree fits metadata notConstructed
  apply ReferenceArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowArgumentCopy
