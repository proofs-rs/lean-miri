import duplicate_prefix.AsMutPtrEntryValidity
import duplicate_prefix.GeneralBorrowFreshReborrowStages

namespace DuplicatePrefix.GenericAsMutPtrEntryValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- Allocator, graph and slice-ownership data for an as_mut_ptr FnEntry retag.
There is no canonical node layout or successful-operation field. -/
structure Data (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) where
  parent : UniIndex
  root : UniIndex
  node : TreeNode
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  parentPresent : tree.nodeAt parent = some node
  roots : tree.roots = #[root]
  covered : GeneralBorrowGraph.RootsCover tree
  tagPresent : tree.indexOfTag parentTag = some parent
  tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  protectorFresh : GeneralBorrowProtector.Fresh tree newTag
  nodeFits : tree.nodes.data.size ≤ 4294967296
  slot : GeneralBorrowFreshReborrowStages.Slot tree depth parent
  well : tree.locations.WellFormed
  owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
    offset (offset+len) tree.locations

/-- Derive the actual runtime validation and protected mutable child ownership
from arbitrary caller-tree data, for append or reused node slots. -/
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
             layout := frame.locals[localId].layout} valid} resultMachine) ∧ GeneralRangeMapOrigins.OwnedOn
        (GeneralBorrowRange.LocationOwned finalTree registered.protectedTags index .Write)
        offset (offset+len) finalTree.locations := by
  let registered := TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag
  let read := entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered.protectedTags .VisitChildrenOfAccessed
  let child := read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
    (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
  have info := RootReferenceInfo.facts options remaining span ctx false
  have mapBounds : offset.toNat+len.toNat ≤ entry.allocation.extra.locations.size.bytes.toNat := by rw [capacity];exact bounds
  have stages := GeneralBorrowFreshReborrowStages.protected_construct entry.allocation.extra tracker.global.protectedTags .mutable
    parentTag tracker.global.nextPointerTag data.parent data.root data.node data.depth data.children data.parentPresent data.roots data.covered
    data.tagPresent data.tagFresh data.protectorFresh data.nodeFits data.slot offset len
    (UInt64.pos_iff_ne_zero.mp positive) data.well mapBounds data.owned
  obtain ⟨index,readDone,childDone,childOwned⟩ := stages
  have childComplete : read.tree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) NestedConstruction.mutableNone)
      ChildBorrow.fnEntryPolicy.outsidePermission true = ⟨child.tree,.ok ()⟩ :=
    GeneralBorrowFreshReborrowStages.child_complete child childDone
  refine ⟨index,?_,childOwned⟩
  exact ProtectedReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    ActualReferenceMetadata.reference .Mut .FnEntry ChildBorrow.fnEntryPolicy NestedConstruction.mutableNone
    rfl (by decide +kernel) (by exact ChildBorrow.mutable_fn_entry_initial_location true) (by decide +kernel)
    info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference
    info.sized info.readable "&mut [u8]" info.named info.classified
    id entry base offset len parentTag positive nonzero signedFits bounds frames frame machine tracker enabled mode
    borrowFrame frameBorrow fresh localId valid live cached ghost shallow cachedAddress present race read.tree child.tree
    rfl readDone childComplete metadata notConstructed

end DuplicatePrefix.GenericAsMutPtrEntryValidity
open Lean Elab Command in
run_cmd do
  for dependency in (←collectAxioms ``DuplicatePrefix.GenericAsMutPtrEntryValidity.positive) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved generic as_mut_ptr entry validity dependency {dependency}"
