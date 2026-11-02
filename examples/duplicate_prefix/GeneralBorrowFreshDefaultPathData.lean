import duplicate_prefix.GeneralBorrowFreshDefaultPathTags
import duplicate_prefix.GeneralBorrowFreshPathExtension
namespace DuplicatePrefix.GeneralBorrowFreshDefaultPathData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
theorem topology_any (tree : BorrowTree) (first second : LocationTree) (firstTags secondTags : ProtectedTags) :
    (source_normal_projection tree first firstTags).topology = (source_normal_projection tree second secondTags).topology := by
  unfold_general_projection
  rfl

noncomputable def forest_of_owned (tree : BorrowTree) (protections : ProtectedTags) (parent : UniIndex) (offset len : UInt64)
    (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (location : LocationTree) (tags : ProtectedTags) :
    GeneralBorrowForest.Forest (source_normal_projection tree location tags).topology := by
  apply Classical.choice
  have lenNonzero : len.toNat ≠ 0 := fun zero => nonzero (UInt64.toNat_inj.mp (by simpa using zero))
  have lenPositive : 0 < len.toNat := by omega
  have sizeBound : tree.locations.size.bytes.toNat < 2^64 := UInt64.toNat_lt_size tree.locations.size.bytes
  have addition : (offset+len).toNat = offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega)]
  have inside : offset.toNat < tree.locations.size.bytes.toNat := by omega
  obtain ⟨position,valid,lower,upper⟩ := GeneralRangeMapGeometry.covered tree.locations well offset inside
  have contract := owned position valid (by omega) (by omega) upper
  rw [←topology_any tree tree.locations.entries[position].data location protections tags]
  exact contract.1

theorem attach (tree : BorrowTree) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (oldLocation newLocation : LocationTree) (tags : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree oldLocation tags).topology) :
    GeneralBorrowFreshSharedPaths.Attach (source_normal_projection tree oldLocation tags).topology
      (source_normal_projection (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) newLocation tags).topology
      parent.toNat (GeneralBorrowFreshMetadataChildDefaultSlot.index slot).toNat := by
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildDefault.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        noFree,aligned,fits,offset,len,nonzero,well,bounds⟩
    have extension := (GeneralBorrowFreshMetadataChildDefault.append input).extension oldLocation newLocation tags
    have atEnd := GeneralBorrowFreshMetadataChildDefault.at_end input
    have projectedSize : (source_normal_projection tree oldLocation tags).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection
      unfold_general_topology
      simp only [Array.size_map]
    have attached := GeneralBorrowFreshSharedPaths.of_append _ _ _ extension forest
    simpa only [GeneralBorrowFreshMetadataChildDefaultSlot.index,GeneralBorrowFreshMetadataChildDefault.index,input,projectedSize] using
      (show GeneralBorrowFreshSharedPaths.Attach _ _ parent.toNat (GeneralBorrowFreshMetadataChildDefault.index input).toNat from by
        rw [atEnd,←projectedSize];exact attached)
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildDefaultReuse.Input :=
      ⟨tree,depth,children,covered,parentTag,newTag,parent,parentNode,parentTagPresent,parentPresent,fresh,
        child,available,bounded,vacant,slack,offset,len,nonzero,well,bounds⟩
    exact GeneralBorrowFreshSharedPaths.of_reuse _ _ _ _
      ((GeneralBorrowFreshMetadataChildDefaultReuse.reuse input).extension oldLocation newLocation tags) forest


theorem build (tree : BorrowTree) (depth : DuplicatePrefix.GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : DuplicatePrefix.GeneralBorrowGraph.ChildNodes tree) (covered : DuplicatePrefix.GeneralBorrowGraph.RootsCover tree)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (parentTagPresent : tree.tagMapping.get parentTag = some parent) (parentPresent : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree depth parent)
    (offset len : UInt64) (nonzero : len ≠ 0) (well : tree.locations.WellFormed)
    (nodeFits : tree.nodes.data.size ≤ 4294967296)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (protections : ProtectedTags) (target : UniIndex) (targetNode : TreeNode)
    (targetPresent : tree.nodeAt target = some targetNode)
    (forest : ∀ location, GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (subset : ∀ location position,
      position ∈ (source_normal_projection tree location protections).topology.ancestorPath target.toNat →
      position ∈ (source_normal_projection tree location protections).topology.ancestorPath parent.toNat)
    (escaping : ∀ location query node, tree.nodeAt query = some node →
      query.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath parent.toNat →
      query.toNat ∉ (source_normal_projection tree location protections).topology.ancestorPath target.toNat →
      protections.contains node.tag = false) :
    (∀ location position,
      position ∈ (source_normal_projection (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) location protections).topology.ancestorPath target.toNat →
      position ∈ (source_normal_projection (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) location protections).topology.ancestorPath
        (GeneralBorrowFreshMetadataChildDefaultSlot.index slot).toNat) ∧
    (∀ location query node, (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len).nodeAt query = some node →
      query.toNat ∈ (source_normal_projection (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) location protections).topology.ancestorPath
        (GeneralBorrowFreshMetadataChildDefaultSlot.index slot).toNat →
      query.toNat ∉ (source_normal_projection (GeneralBorrowFreshMetadataChildDefaultSlot.result tree parentTag newTag offset len) location protections).topology.ancestorPath target.toNat →
      protections.contains node.tag = false ∨ node.tag = newTag) := by
  have metadata := GeneralBorrowFreshMetadataChildDefaultSlot.build tree depth children covered parentTag newTag parent parentNode
    parentTagPresent parentPresent fresh slot offset len nonzero well nodeFits bounds
  have targetBound := GeneralBorrowNodeUpdate.lookup_valid tree.nodes target targetNode targetPresent
  have valid : ∀ location, target.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    intro location
    unfold_general_projection
    unfold_general_topology
    simpa only [Array.size_map] using targetBound
  have attached := fun location => attach tree depth children covered parentTag newTag parent parentNode parentTagPresent parentPresent
    fresh slot offset len nonzero well bounds location location protections (forest location)
  refine ⟨?_,?_⟩
  · intro location position member
    exact GeneralBorrowFreshPathExtension.subset _ _ parent.toNat _ target.toNat (attached location) (valid location) (subset location) position member
  · intro location query node present localChild foreignTarget
    by_cases isNew : query = GeneralBorrowFreshMetadataChildDefaultSlot.index slot
    · subst query
      obtain ⟨newNode,lookup,tag,_⟩ := metadata.node
      have equal : node = newNode := Option.some.inj (present.symm.trans lookup)
      cases equal
      exact Or.inr tag
    · have split := GeneralBorrowFreshPathExtension.escaping _ _ parent.toNat _ target.toNat query.toNat
        (attached location) (valid location) (subset location) localChild foreignTarget
      rcases split with same | old
      · exact False.elim (isNew (GeneralBorrowNodeUpdate.index_injective _ _ same))
      · obtain ⟨original,lookup,tagEq⟩ := GeneralBorrowFreshDefaultPathTags.of_slot tree depth children covered parentTag newTag parent parentNode
          parentTagPresent parentPresent fresh slot offset len nonzero well bounds query node present isNew
        apply Or.inl
        rw [tagEq]
        exact escaping location query original lookup old.1 old.2
end DuplicatePrefix.GeneralBorrowFreshDefaultPathData
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshDefaultPathData." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mutable initial path dependency {dependency}"
