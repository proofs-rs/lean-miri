import duplicate_prefix.GeneralBorrowDirectParentGeometry
import duplicate_prefix.GeneralBorrowParentRestoreScalar
import duplicate_prefix.GeneralBorrowFreshProtectorRelease
import duplicate_prefix.GeneralBorrowNormalPermissionMetadata
import duplicate_prefix.GeneralBorrowStructuralHistoryState
namespace DuplicatePrefix.GeneralBorrowParentRestoreNormal
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Direct-child reanchoring after protector weakening. Descendants, siblings,
other roots and the actual current permissions are arbitrary. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (before after : ProtectedTags)
    (child parent : UniIndex) (childNode : TreeNode)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (present : tree.nodeAt child = some childNode) (edge : childNode.parent = some parent)
    (weaken : ∀ tag, after.contains tag = true → before.contains tag = true)
    (absent : after.contains childNode.tag = false)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location before child) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location after parent) := by
  obtain ⟨forest⟩ := formed.forest location before
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child childNode present
  have projectedEdge : (nodeData (source_normal_projection tree location before).topology child.toNat).parent = some parent.toNat := by
    change ((source_normal_projection tree location before).topology.nodes[child.toNat]?.getD ⟨none,[]⟩).parent = _
    rw [projection_topology_node tree location before child.toNat child childNode rfl present]
    simp only [edge,Option.map_some]
  have projectionSize : (source_normal_projection tree location before).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have bounded : child.toNat < (source_normal_projection tree location before).topology.nodes.size := by rw [projectionSize];exact valid
  have paths := GeneralBorrowDirectParentGeometry.paths _ forest child.toNat parent.toNat bounded (by
    simpa only [nodeData,Array.getElem?_eq_getElem bounded,Option.getD_some] using projectedEdge)
  have parentSupported := old.component.parents child.toNat old.component.anchor parent.toNat projectedEdge
  let component : GeneralBorrowExposedScopedNormal.Component (source_normal_projection tree default after).topology parent.toNat :=
    ⟨old.component.support,parentSupported,old.component.parents,old.component.children⟩
  refine ⟨⟨component,?_⟩⟩
  intro kind index included boundedIndex
  obtain ⟨state,stored,compatible⟩ := old.permissions kind index included boundedIndex
  refine ⟨state,stored,?_⟩
  by_cases same : index = child.toNat
  · subst index
    have foreign : relation (source_normal_projection tree location after) parent.toNat child.toNat = .ForeignAccess := by
      simp only [relation,show child.toNat ∉ (source_normal_projection tree location after).topology.ancestorPath parent.toNat from paths.2,ite_false]
    rw [foreign,GeneralBorrowNormalPermissionMetadata.held tree location after child childNode present,absent]
    cases kind <;> exact ⟨compatible.1,by simp⟩
  · have relations : relation (source_normal_projection tree location after) parent.toNat index =
        relation (source_normal_projection tree location before) child.toNat index := by
      change relation (source_normal_projection tree location before) parent.toNat index = _
      unfold relation
      rw [paths.1]
      simp only [List.mem_cons,same,false_or]
    rw [relations]
    exact GeneralBorrowParentRestoreScalar.weakens state kind _ _ _
      (GeneralBorrowFreshProtectorRelease.projection_weakens tree location before after weaken index) compatible

/-- The real endCall bookkeeping supplies both weakening and absence for a
frame-owned child tag. This statement does not execute releaseProtector. -/
theorem end_call (tree : BorrowTree) (location : LocationTree) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (child parent : UniIndex) (childNode : TreeNode)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (present : tree.nodeAt child = some childNode) (edge : childNode.parent = some parent)
    (registered : (allocation,childNode.tag) ∈ frame.protectedTags.toList)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags child) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location (global.endCall frame).protectedTags parent) :=
  normal tree location _ _ child parent childNode formed present edge
    (GeneralBorrowRelease.end_call_weakens global frame)
    (GeneralBorrowRelease.end_call_owned_absent global frame allocation childNode.tag registered) old
end DuplicatePrefix.GeneralBorrowParentRestoreNormal
