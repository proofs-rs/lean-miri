import duplicate_prefix.S02WildcardSameDestinationRootTopology
import duplicate_prefix.S02ConstructorOutsideProjection
namespace DuplicatePrefix.S02WildcardSameDestinationRootNormal
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowNodeUpdate GeneralBorrowPresence S02ConstructorOutsideProjection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert
/-- Isolated-root insertion preserves an old arbitrary normal component;
a reused vacant slot may already occur in its support. -/
theorem normal (tree : BorrowTree) (graph : GeneralBorrowStructuralHistoryState.GraphState tree)
    (index source : UniIndex) (tag : BorTag) (sourceNode : TreeNode)
    (vacant : tree.nodes.get index = none) (sourcePresent : tree.nodeAt source = some sourceNode)
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (location : LocationTree) (protections : ProtectedTags) (clean : location.perms.get index = none)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location protections source) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      {tree with nodes := tree.nodes.insert index (WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None)}
      location protections source) := by
  let node := WildcardHitZeroConstructor.rootNode tag (.ReservedFrz false) .None
  let after : BorrowTree := {tree with nodes := tree.nodes.insert index node}
  have shape := S02WildcardSameDestinationRootTopology.nodes tree index node vacant rfl rfl slot location protections
  have defaultShape := S02WildcardSameDestinationRootTopology.nodes tree index node vacant rfl rfl slot default protections
  have sameData := S02WildcardSameDestinationRootTopology.data _ _ defaultShape
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection after default protections).topology source.toNat := {
    support := old.component.support,
    anchor := old.component.anchor,
    parents := by intro current included parent edge;rw [sameData] at edge;exact old.component.parents current included parent edge,
    children := by intro current included child member;rw [sameData] at member;exact old.component.children current included child member }
  obtain ⟨forest⟩ := graph.forest location protections
  have sourceValid : source.toNat < (source_normal_projection tree location protections).topology.nodes.size := by
    rw [topology_size];exact lookup_valid tree.nodes source sourceNode sourcePresent
  have path := S02WildcardSameDestinationRootTopology.path _ _ shape forest source.toNat sourceValid
  have pathEq : (source_normal_projection after location protections).topology.ancestorPath source.toNat = (source_normal_projection tree location protections).topology.ancestorPath source.toNat := path
  have different (query : UniIndex) (value : TreeNode) (present : tree.nodeAt query = some value) : query ≠ index := by
    intro same
    change tree.nodes.get query = some value at present
    rw [same,vacant] at present;cases present
  refine ⟨⟨component,?_⟩⟩
  intro kind position included valid
  by_cases fresh : position = index.toNat
  · subst position
    have present : after.nodeAt index = some node := GeneralBorrowFreshLocation.get_same tree.nodes index node
    have state : (source_normal_projection after location protections).stateAt index.toNat = some ⟨.ReservedFrz false,false,.None⟩ := by
      rw [projection_state after location protections index.toNat index node (index_self index) rfl present,clean]
      rfl
    exact ⟨_,state,S02ConstructorNormalTopology.lazy_compatible kind _ _ .None⟩
  · have oldValid : position < tree.nodes.data.size := by
      have newValid : position < (source_normal_projection after location protections).topology.nodes.size := by rw [topology_size];exact valid
      rcases shape with same | appended
      · rw [same,topology_size] at newValid;exact newValid
      · rw [appended,Array.size_push,topology_size] at newValid
        rcases slot with atEnd | bounded
        · omega
        · have actualSize := GeneralBorrowFreshReuseNode.bounded_size tree.nodes index node bounded
          change after.nodes.size = tree.nodes.size at actualSize
          change position < after.nodes.size at valid
          rw [actualSize] at valid;exact valid
    obtain ⟨query,converted,equal⟩ := index_nat position (by have fits:=graph.fits;change tree.nodes.data.size ≤ _ at fits;omega)
    have queryDifferent : query ≠ index := by intro same;exact fresh (equal.symm.trans (congrArg UniIndex.toNat same))
    have lookup : after.nodeAt query = tree.nodeAt query := GeneralBorrowFreshLocation.get_other tree.nodes index query node queryDifferent
    have state : (source_normal_projection after location protections).stateAt position = (source_normal_projection tree location protections).stateAt position := by
      rw [projection_slot after location protections position query converted equal valid,
        projection_slot tree location protections position query converted equal oldValid,lookup]
    have protectionEq : (source_normal_projection after location protections).protectedNodes.contains position = (source_normal_projection tree location protections).protectedNodes.contains position := by
      rw [←equal]
      apply Bool.eq_iff_iff.mpr
      simp only [List.contains_iff_mem,GeneralBorrowFreshReuseProtection.protected_iff,lookup]
    obtain ⟨value,stored,compatible⟩ := old.permissions kind position included oldValid
    refine ⟨value,state.trans stored,?_⟩
    change DuplicatePrefixScalarAuthorization.Compatible value kind
      (GeneralBorrowAnchor.relation (source_normal_projection after location protections) source.toNat position)
      ((source_normal_projection after location protections).protectedNodes.contains position)
    unfold GeneralBorrowAnchor.relation
    rw [pathEq,protectionEq]
    exact compatible
end DuplicatePrefix.S02WildcardSameDestinationRootNormal
