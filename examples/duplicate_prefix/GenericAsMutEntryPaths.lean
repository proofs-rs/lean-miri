import duplicate_prefix.GenericAsMutEntryTree
import duplicate_prefix.GeneralBorrowFreshMutablePathData
import duplicate_prefix.GeneralBorrowFreshMetadataChildAllocator
namespace DuplicatePrefix.GenericAsMutEntryPaths
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralRangeMapState GeneralBorrowFreshReadFrame GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem prepare (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (parentTag : BorTag) (offset len : UInt64)
    (data : GenericAsMutPtrEntryValidity.Data tree tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (subset : ∀ location position,
      position ∈ (source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath target.toNat →
      position ∈ (source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath data.parent.toNat)
    (escaping : ∀ location query node, tree.nodeAt query = some node →
      query.toNat ∈ (source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath data.parent.toNat →
      query.toNat ∉ (source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath target.toNat →
      tracker.global.protectedTags.contains node.tag = false) :
    let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
    let tags := (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    (∀ location position,
      position ∈ (source_normal_projection after location tags).topology.ancestorPath target.toNat →
      position ∈ (source_normal_projection after location tags).topology.ancestorPath (GeneralBorrowFreshMutableStages.slot_index data.slot).toNat) ∧
    (∀ location query node, after.nodeAt query = some node →
      query.toNat ∈ (source_normal_projection after location tags).topology.ancestorPath (GeneralBorrowFreshMutableStages.slot_index data.slot).toNat →
      query.toNat ∉ (source_normal_projection after location tags).topology.ancestorPath target.toNat →
      tags.contains node.tag = false ∨ node.tag = tracker.global.nextPointerTag) := by
  let newTag := tracker.global.nextPointerTag
  let registered := tracker.global.protectedTags.insert newTag .StrongProtector
  let read := tree.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read registered .VisitChildrenOfAccessed
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
  have childIndex : GeneralBorrowFreshMetadataChildMutableSlot.index readSlot = GeneralBorrowFreshMutableStages.slot_index data.slot := slotIndex.trans indexEq
  have readTarget : read.tree.nodeAt target = some targetNode := by
    change read.tree.nodes.get target = some targetNode
    rw [nodes]
    exact targetPresent
  have readSubset : ∀ location position,
      position ∈ (source_normal_projection read.tree location tracker.global.protectedTags).topology.ancestorPath target.toNat →
      position ∈ (source_normal_projection read.tree location tracker.global.protectedTags).topology.ancestorPath data.parent.toNat := by
    intro location position member
    have topology := GeneralBorrowFreshMetadataChildAllocator.topology_frame tree read.tree nodes location location tracker.global.protectedTags
    rw [topology] at member ⊢
    exact subset location position member
  have readEscaping : ∀ location query node, read.tree.nodeAt query = some node →
      query.toNat ∈ (source_normal_projection read.tree location tracker.global.protectedTags).topology.ancestorPath data.parent.toNat →
      query.toNat ∉ (source_normal_projection read.tree location tracker.global.protectedTags).topology.ancestorPath target.toNat →
      tracker.global.protectedTags.contains node.tag = false := by
    intro location query node present localParent foreignTarget
    have topology := GeneralBorrowFreshMetadataChildAllocator.topology_frame tree read.tree nodes location location tracker.global.protectedTags
    rw [topology] at localParent foreignTarget
    change read.tree.nodes.get query = some node at present
    rw [nodes] at present
    exact escaping location query node present localParent foreignTarget
  have paths := GeneralBorrowFreshMutablePathData.build read.tree readDepth graph.1 graph.2 parentTag newTag data.parent data.node
    parentTagPresent parentPresent fresh readSlot offset len nonzero readWell readFits readBounds tracker.global.protectedTags target targetNode readTarget
    (fun location => GeneralBorrowFreshMutablePathData.forest_of_owned read.tree registered data.parent offset len nonzero readWell readBounds
      readGood.2.1 location tracker.global.protectedTags) readSubset readEscaping
  rw [childIndex] at paths
  let after := GenericAsMutPtrArgumentCopy.finalTree tree tracker parentTag offset len
  have topology : ∀ location, (source_normal_projection after location registered).topology =
      (source_normal_projection after location tracker.global.protectedTags).topology :=
    fun location => GeneralBorrowFreshMutablePathData.topology_any after location location registered tracker.global.protectedTags
  refine ⟨?_,?_⟩
  · intro location position member
    change position ∈ (source_normal_projection after location registered).topology.ancestorPath target.toNat at member
    change position ∈ (source_normal_projection after location registered).topology.ancestorPath (GeneralBorrowFreshMutableStages.slot_index data.slot).toNat
    rw [topology location] at member ⊢
    exact paths.1 location position member
  · intro location query node present localChild foreignTarget
    change query.toNat ∈ (source_normal_projection after location registered).topology.ancestorPath (GeneralBorrowFreshMutableStages.slot_index data.slot).toNat at localChild
    change query.toNat ∉ (source_normal_projection after location registered).topology.ancestorPath target.toNat at foreignTarget
    rw [topology location] at localChild foreignTarget
    have classified := paths.2 location query node present localChild foreignTarget
    rcases classified with old | new
    · by_cases same : node.tag = newTag
      · exact Or.inr same
      · apply Or.inl
        change (tracker.global.protectedTags.insert newTag .StrongProtector).contains node.tag = false
        rw [ProtectorInsertion.contains_other tracker.global.protectedTags newTag node.tag .StrongProtector same]
        exact old
    · exact Or.inr new
end DuplicatePrefix.GenericAsMutEntryPaths
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GenericAsMutEntryPaths." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved initial entry path dependency {dependency}"
