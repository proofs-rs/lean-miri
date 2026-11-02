import duplicate_prefix.AsMutPtrEntryValidity
import duplicate_prefix.GeneralBorrowForestFnEntry

namespace DuplicatePrefix.GeneralBorrowForestEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- Multiple-root mutable FnEntry initial data. Global unheld is independent
of map freshness. Graph, ownership, BOTH cache-kind region records and physical
runtime/compiler premises are explicit; there is no successful-operation field. -/
structure Data (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) where
  parent : UniIndex
  primary : UniIndex
  extras : List UniIndex
  context : GeneralBorrowForestAccessData.Context tree parent primary extras
  covered : GeneralBorrowGraph.RootsCover tree
  tagPresent : tree.indexOfTag parentTag = some parent
  tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  globalUnheld : protections.get newTag = none
  nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index
  nodeFits : tree.nodes.data.size ≤ 4294967296
  slot : GeneralBorrowFreshReborrowStages.Slot tree context.depth parent
  well : tree.locations.WellFormed
  owned : GeneralRangeMapOrigins.OwnedOn
    (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections parent primary extras))
    offset (offset+len) tree.locations

/-- Derive the actual runtime validation and protected mutable child ownership
from multiple-root caller-tree data, actual Strong registration, and either
append or reused node slots. This is real typed runtime validation, not yet a
whole MIR invocation or every valid-history classification. -/
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
    (data : Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
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
    ∃ index, ValidityMachine.validateRuntime cfg.validity () (validityFuel+1)
      (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference) true
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame frame borrowFrame id tracker.global.nextPointerTag) with
          locals := frame.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm),
             layout := frame.locals[localId].layout} valid} resultMachine) ∧ Nonempty (GeneralBorrowForestAccessData.Context finalTree index data.primary data.extras) ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data finalTree location registered.protectedTags index data.primary data.extras))
        offset (offset+len) finalTree.locations := by
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  have info := RootReferenceInfo.facts options remaining span ctx false
  have mapBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have registeredData := GeneralBorrowForestMutableRegister.registered entry.allocation.extra tracker.global borrowFrame id
    tracker.global.nextPointerTag .StrongProtector data.parent data.primary data.extras data.tagFresh data.nodeTags
    data.globalUnheld offset (offset+len) data.owned
  have stages := GeneralBorrowForestProtected.run entry.allocation.extra registered.protectedTags parentTag tracker.global.nextPointerTag
    data.parent data.primary data.extras offset len .VisitChildrenOfAccessed data.context data.covered data.tagPresent data.tagFresh data.slot
    data.nodeFits (UInt64.pos_iff_ne_zero.mp positive) data.well mapBounds registeredData.2.2.2
  change read.status = .Completed ∧ child.outcome = .ok () ∧
    Nonempty (GeneralBorrowForestAccessData.Context child.tree (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) data.primary data.extras) ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data child.tree location registered.protectedTags
        (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) data.primary data.extras)) offset (offset+len) child.tree.locations ∧
    child.tree.indexOfTag tracker.global.nextPointerTag = some (GeneralBorrowFreshMetadataChildMutableSlot.index data.slot) ∧
    child.tree.locations.WellFormed ∧ child.tree.locations.size = entry.allocation.extra.locations.size ∧
    child.tree.nodes.data.size ≤ 4294967296 ∧ GeneralBorrowGraph.RootsCover child.tree at stages
  have readDone := stages.1
  have childDone := stages.2.1
  have childComplete : read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) NestedConstruction.mutableNone)
      ChildBorrow.fnEntryPolicy.outsidePermission true = ⟨child.tree,.ok ()⟩ :=
    GeneralBorrowFreshReborrowStages.child_complete child childDone
  refine ⟨GeneralBorrowFreshMetadataChildMutableSlot.index data.slot,?_,stages.2.2.1,stages.2.2.2.1⟩
  exact ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    ActualReferenceMetadata.reference .Mut .FnEntry ChildBorrow.fnEntryPolicy NestedConstruction.mutableNone
    rfl (by decide +kernel) (by exact ChildBorrow.mutable_fn_entry_initial_location true) (by decide +kernel)
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&mut [u8]" info.named info.classified
    id entry base offset len parentTag positive nonzero signedFits bounds frames frame machine tracker enabled mode
    borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress present race read.tree child.tree
    rfl readDone childComplete metadata notConstructed

end DuplicatePrefix.GeneralBorrowForestEntryValidity
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GeneralBorrowForestEntryValidity.positive) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved forest as_mut_ptr entry validity dependency {dependency}"
