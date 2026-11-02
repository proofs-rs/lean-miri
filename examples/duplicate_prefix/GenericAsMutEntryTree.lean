import duplicate_prefix.GenericAsMutPtrArgumentCopy
import duplicate_prefix.GenericAsMutReleasePlan
import duplicate_prefix.GeneralBorrowFreshMutableActivity
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableOld

namespace DuplicatePrefix.GenericAsMutEntryTree
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowFreshReadFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- The actual FnEntry mutable tree has the helper-release contract, from
initial graph/ownership and a clean allocator slot. The older anchor's strong
activity is derived through the same real Read and constructor. -/
theorem prepare (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (parentTag : BorTag) (offset len : UInt64)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag
      tracker.global.nextPointerTag offset len)
    (positive : offset.toNat < (offset+len).toNat) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : Every (fun location : LocationTree => location.perms.get
      (GeneralBorrowFreshMutableStages.slot_index data.slot) = none) tree.locations)
    (target : UniIndex)
    (targetWithin : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write offset (offset+len)) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    let registered := (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    ∃ release : GenericAsMutReleasePlan.Input after registered tracker.global.nextPointerTag,
      release.anchor = GeneralBorrowFreshMutableStages.slot_index data.slot ∧
      release.lower = offset ∧ release.upper = offset+len ∧
      after.locations.size = tree.locations.size ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin after target .Write offset (offset+len) ∧
      (∀ tag, tracker.global.nextPointerTag ≠ tag → after.indexOfTag tag = tree.indexOfTag tag) ∧
      (∀ query oldNode, tree.nodeAt query = some oldNode →
        ∃ next, after.nodeAt query = some next ∧ next.tag = oldNode.tag ∧ next.isExposed = oldNode.isExposed) := by
  let newTag := tracker.global.nextPointerTag
  let registered := tracker.global.protectedTags.insert newTag .StrongProtector
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have stages := GeneralBorrowFreshMutableStages.borrow tree tracker.global.protectedTags parentTag newTag
    data.parent data.root data.node data.depth data.children data.parentPresent data.roots data.covered data.tagPresent
    data.tagFresh data.protectorFresh data.nodeFits data.slot offset len nonzero data.well bounds data.owned clean
  have oldStrong := GeneralBorrowFreshMutableActivity.preserves_target tree tracker.global.protectedTags parentTag newTag
    data.parent data.root data.node data.depth data.children data.parentPresent data.roots data.covered data.tagPresent
    data.tagFresh data.protectorFresh data.nodeFits data.slot offset len nonzero data.well bounds data.owned
    target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) targetWithin
  have framed := frame tree (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
  have nodeEq := congrArg BorrowTree.nodes framed
  have nodes : read.tree.nodes = tree.nodes := nodeEq
  have tagEq := congrArg BorrowTree.tagMapping framed
  have tags : read.tree.tagMapping = tree.tagMapping := tagEq
  have rootEq := congrArg BorrowTree.roots framed
  have roots : read.tree.roots = tree.roots := rootEq
  let readDepth := depth_on tree read.tree nodes data.depth
  have graph : GeneralBorrowGraph.ChildNodes read.tree ∧ GeneralBorrowGraph.RootsCover read.tree := by
    rw [framed]
    exact graph_on tree read.tree.locations data.children data.covered
  let readSlot := GeneralBorrowFreshMetadataChildMutableSlot.transport tree read.tree data.depth readDepth
    nodes tags rfl data.parent data.slot
  have slotIndex := GeneralBorrowFreshMetadataChildMutableSlot.transport_index tree read.tree data.depth readDepth
    nodes tags rfl data.parent data.slot
  have indexEq : GeneralBorrowFreshMetadataChildMutableSlot.index data.slot =
      GeneralBorrowFreshMutableStages.slot_index data.slot := by cases data.slot <;> rfl
  have parentPresent : read.tree.nodeAt data.parent = some data.node := by
    change read.tree.nodes.get data.parent = some data.node
    rw [nodes]
    exact data.parentPresent
  have parentTagPresent : read.tree.indexOfTag parentTag = some data.parent := by
    change read.tree.tagMapping.get parentTag = some data.parent
    rw [tags]
    exact data.tagPresent
  have fresh : GeneralBorrowTagMap.Fresh read.tree.tagMapping newTag := by rw [tags];exact data.tagFresh
  have registeredOwned := protector_owned_on tree tracker.global.protectedTags newTag .StrongProtector
    data.protectorFresh data.parent .Write offset (offset+len) data.owned
  have readGood := GeneralBorrowRangeLocal.access tree registered parentTag data.parent data.root
    (Size.ofBytes offset) (Size.ofBytes len) .Read .Write .VisitChildrenOfAccessed (fun _ => rfl)
    data.nodeFits data.depth data.children data.node data.parentPresent data.roots data.covered data.tagPresent
    data.well offset (offset+len) registeredOwned bounds (Nat.le_refl _) (Nat.le_refl _)
  have readWell : read.tree.locations.WellFormed := readGood.2.2.1
  have readSize : read.tree.locations.size = tree.locations.size := readGood.2.2.2
  have readBounds : offset.toNat+len.toNat ≤ read.tree.locations.size.bytes.toNat := by rw [readSize];exact bounds
  have readFits : read.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact data.nodeFits
  let metadata := GeneralBorrowFreshMetadataChildMutableSlot.build read.tree readDepth graph.1 graph.2
    parentTag newTag data.parent data.node parentTagPresent parentPresent fresh readSlot offset len nonzero readWell readFits readBounds
  have childIndex : GeneralBorrowFreshMetadataChildMutableSlot.index readSlot =
      GeneralBorrowFreshMutableStages.slot_index data.slot := slotIndex.trans indexEq
  obtain ⟨node,nodePresent,nodeTag,notExposed⟩ := metadata.node
  rw [childIndex] at nodePresent
  have lookup := metadata.lookup
  rw [childIndex] at lookup
  let release : GenericAsMutReleasePlan.Input
      (GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len)
      (TypedBorrowSteps.registeredGlobal tracker newTag).protectedTags newTag := {
    anchor := GeneralBorrowFreshMutableStages.slot_index data.slot
    root := data.root
    lower := offset
    upper := offset+len
    positive := positive
    fits := metadata.nodeFits
    depth := metadata.certificates.depth
    children := metadata.certificates.children
    node := node
    anchorPresent := nodePresent
    notExposed := notExposed
    roots := metadata.roots.trans (roots.trans data.roots)
    covered := metadata.certificates.covered
    tagPresent := lookup
    well := metadata.well
    within := stages.2.2.2
    owned := stages.2.2.1 }
  refine ⟨release,rfl,rfl,rfl,metadata.capacity.trans readSize,oldStrong,?_,?_⟩
  · intro tag different
    exact (metadata.oldLookup tag different).trans (congrArg (fun mapping => mapping.get tag) tags)
  · intro query oldNode present
    have presentAfter : read.tree.nodeAt query = some oldNode := by
      change read.tree.nodes.get query = some oldNode
      rw [nodes]
      exact present
    exact GeneralBorrowFreshMetadataChildMutableOld.of_slot read.tree readDepth graph.1 graph.2 parentTag newTag
      data.parent data.node parentTagPresent parentPresent fresh readSlot offset len nonzero readWell readBounds
      query oldNode presentAfter

end DuplicatePrefix.GenericAsMutEntryTree
