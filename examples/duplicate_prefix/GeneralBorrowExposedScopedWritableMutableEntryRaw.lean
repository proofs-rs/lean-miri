import duplicate_prefix.GeneralBorrowExposedScopedMutableEntryValidity
import duplicate_prefix.GeneralBorrowExposedScopedWritableMutableEntryData
namespace DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryRaw
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
structure Data (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (selected head : UniIndex) (tail : List UniIndex) where
  input : GeneralBorrowFreshMetadataChildMutable.Input
  treeEq : input.tree = tree
  parentTagEq : input.parentTag = parentTag
  newTagEq : input.newTag = newTag
  offsetEq : input.offset = offset
  lenEq : input.len = len
  resources : GeneralBorrowExposedScopedWritableProtectedMutableConstructor.Resources input protections selected head tail
  nodeTags : GeneralBorrowGcAllocator.NodeTags tree
/-- Actual protected mutable runtime validation follows from initial scoped
resources; Strong registration and both borrow operations are derived. -/
theorem positive
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
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
    (data : Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len selected head tail)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len ActualReferenceMetadata.reference).imm))
    (cached : frame.locals[localId].layout = some ActualReferenceMetadata.reference)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
    let read := entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
      .Read registered.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    let finalTree := child.tree
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag) with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) := by
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedWritableMutableEntryData.registered data.input tracker.global.protectedTags
    selected head tail data.resources (by simpa only [data.treeEq] using data.nodeTags)
  simp only [data.treeEq,data.newTagEq,data.offsetEq,data.lenEq] at context owned
  have mixed : GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedScopedMixedRangeData.Data entry.allocation.extra location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags data.input.parent selected head tail
        data.resources.component.support (fun _=>true))) offset (offset+len) entry.allocation.extra.locations := by
    intro position valid positive lower upper
    obtain ⟨row⟩:=owned position valid positive lower upper
    exact ⟨row.base⟩
  exact GeneralBorrowExposedScopedMutableEntryValidity.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames frame machine tracker enabled mode borrowFrame frameBorrow fresh
    data.input.parent selected head tail context (by simpa only [data.treeEq] using data.input.covered)
    (by simpa only [data.treeEq] using data.resources.forest)
    (by simpa only [data.treeEq,data.parentTagEq,BorrowTree.indexOfTag] using data.input.parentTagPresent)
    (by simpa only [data.treeEq,data.newTagEq] using data.input.fresh)
    (by simpa only [data.treeEq] using data.input.noFree)
    (by simpa only [data.treeEq] using data.input.aligned)
    (by simpa only [data.treeEq] using data.input.fits)
    data.resources.component.support (by simpa only [data.treeEq] using data.input.well) mixed capacity
    localId valid live cached ghost shallow cachedAddress present race metadata notConstructed
end DuplicatePrefix.GeneralBorrowExposedScopedWritableMutableEntryRaw
