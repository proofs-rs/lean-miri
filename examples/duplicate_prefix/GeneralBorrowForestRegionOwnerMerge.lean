import duplicate_prefix.GeneralBorrowWildcardSubtreeRegion
import duplicate_prefix.GeneralBorrowFreshReuseProtection

namespace DuplicatePrefix.GeneralBorrowForestRegionOwnerMerge
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
open DuplicatePrefix.GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A present node's projected protector bit is exactly its real tag-table bit. -/
theorem held_present (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (index : UniIndex) (node : TreeNode) (present : tree.nodeAt index = some node) :
    (source_normal_projection tree location protections).protectedNodes.contains index.toNat = protections.contains node.tag := by
  have selected : (source_normal_projection tree location protections).protectedNodes.contains index.toNat = true ↔
      protections.contains node.tag = true := by
    rw [List.contains_iff_mem,GeneralBorrowFreshReuseProtection.protected_iff]
    constructor
    · rintro ⟨actual,found,held⟩
      have same := Option.some.inj (present.symm.trans found)
      subst actual
      exact held
    · intro held
      exact ⟨node,present,held⟩
  cases left : (source_normal_projection tree location protections).protectedNodes.contains index.toNat <;>
    cases right : protections.contains node.tag <;> simp_all

private theorem slot (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (index : UniIndex) (converted : UniIndex.ofNat? position = some index) (equal : index.toNat = position)
    (valid : position < tree.nodes.data.size) :
    (source_normal_projection tree location protections).stateAt position =
      some ((location.perms.get index).getD
        (((tree.nodeAt index).map TreeNode.defaultLocationState).getD ⟨.Disabled,false,.None⟩)) := by
  have nodeValue : tree.nodeAt index = tree.nodes.data[position]'valid := by
    unfold BorrowTree.nodeAt UniValMap.get
    simp only [equal,Array.getElem?_eq_getElem valid]
  unfold_general_projection
  unfold NormalTreeState.stateAt
  simp only [Array.getElem?_mapIdx,Array.getElem?_map,Array.getElem?_eq_getElem valid,converted,Option.map_some]
  rw [nodeValue]
  cases stored : location.perms.get index <;> cases tree.nodes.data[position] <;> rfl

/-- Pure merge of the actual normal owner poststate with a foreign common-region
poststate. The region remains foreign to this anchor, and permissions outside
it retain their exact normal values. No operation or success premise appears. -/
theorem merge (tree : BorrowTree) (initial normal after : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (ownerKind opKind : AccessKind) (fits : tree.nodes.data.size ≤ 4294967296)
    (region : Region tree initial opKind protections)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree normal protections) anchor.toNat ownerKind)
    (regionOwned : Owned region after)
    (outside : ∀ query, ¬region.support query → after.perms.get query = normal.perms.get query)
    (foreignGraph : ∀ query, region.support query →
      query.toNat ∉ (source_normal_projection tree normal protections).topology.ancestorPath anchor.toNat) :
    GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree after protections) anchor.toNat ownerKind := by
  have size : (source_normal_projection tree after protections).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  refine ⟨owned.anchorValid,(projection_sizes tree after protections).1.trans size.symm,owned.defaultsAligned,?_⟩
  intro position valid
  have bounded : position < tree.nodes.data.size := by
    have size : (source_normal_projection tree after protections).topology.nodes.size = tree.nodes.data.size := by
      unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
    rw [size] at valid
    exact valid
  obtain ⟨index,converted,equal⟩ := index_nat position (by omega)
  by_cases supported : region.support index
  · obtain ⟨node,present⟩ := region.present index supported
    refine ⟨GeneralBorrowWildcardVirtualLeaf.effective after index node,?_,?_⟩
    · rw [projection_state tree after protections position index node converted equal present]
      rfl
    · have foreign := foreignGraph index supported
      change GeneralBorrowPermissions.AccessOwned _ ownerKind
        (if position ∈ (source_normal_projection tree normal protections).topology.ancestorPath anchor.toNat then .LocalAccess else .ForeignAccess) _
      rw [←equal,ite_eq_right foreign,held_present tree after protections index node present]
      cases ownerKind <;> exact regionOwned index node supported present
  · obtain ⟨state,present,permitted⟩ := owned.permissions position valid
    refine ⟨state,?_,permitted⟩
    rw [slot tree after protections position index converted equal bounded,
      outside index supported,←slot tree normal protections position index converted equal bounded]
    exact present

end DuplicatePrefix.GeneralBorrowForestRegionOwnerMerge
