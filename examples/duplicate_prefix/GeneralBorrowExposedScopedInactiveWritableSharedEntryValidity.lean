import duplicate_prefix.ProtectedReferenceValidator
import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedAppend
import duplicate_prefix.GeneralBorrowFreshReborrowStages
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
/-- Physical shared FnEntry validation on multiple roots. Initial registered-map
permission/cache records and physical metadata remain explicit. Real Read,
Frozen construction, Strong registration and runtime validation are derived. -/
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
    (parent selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context entry.allocation.extra parent selected head tail)
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (forest : GeneralBorrowForest.Forest (source_normal_projection entry.allocation.extra default tracker.global.protectedTags).topology)
    (tagPresent : entry.allocation.extra.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (support : Nat → Prop) (writable : Nat → Bool) (well : entry.allocation.extra.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data entry.allocation.extra location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags parent selected head tail support writable))
      offset (offset+len) entry.allocation.extra.locations)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (RetagReferencePlace.sliceValue
      (config options remaining span).access.runtime.base (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset)))
      len SharedReferenceMetadata.sharedLayout).imm))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
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
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) NestedConstruction.frozenRead) (.Frozen) true
    let finalTree := child.tree
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
  have mapBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have successes := GeneralBorrowExposedScopedInactiveWritableSharedAppend.append entry.allocation.extra
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    parentTag tracker.global.nextPointerTag parent selected head tail offset len
    context covered forest tagPresent tagFresh noFree aligned fits true support writable
    (UInt64.pos_iff_ne_zero.mp positive) well mapBounds owned
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) frozenRead) .Frozen true
  have readDone : read.status = .Completed := successes.1
  have childDone : child.outcome = .ok () := by
    simpa only [child, read, GeneralBorrowFreshAnchor.sharedState, frozenRead] using successes.2.1
  have childComplete : read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) frozenRead) (sharedPolicy true).outsidePermission true =
        ⟨child.tree,.ok ()⟩ := GeneralBorrowFreshReborrowStages.child_complete child childDone
  exact ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
      SharedReferenceMetadata.sharedLayout .Not .FnEntry (sharedPolicy true) frozenRead
      rfl (by decide +kernel) (shared_initial true) shared_entry_policy
      info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
      info.sized info.readable "&[u8]" info.named info.classified
      id entry base offset len parentTag positive nonzero signedFits bounds frames frame machine tracker enabled mode
      borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress present race read.tree child.tree
      rfl readDone childComplete metadata notConstructed
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedEntryValidity
