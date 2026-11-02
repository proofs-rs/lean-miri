import duplicate_prefix.GeneralBorrowFreshLifetimeRestore
import duplicate_prefix.GeneralBorrowFreshReuseProtection
namespace DuplicatePrefix.GeneralBorrowFreshRestoreData
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Protected projection membership has a real node/tag witness even for
arbitrary natural positions. Ghost/sparse positions cannot invent protection. -/
theorem protected_witness (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (position : Nat) (held : (source_normal_projection tree location protections).protectedNodes.contains position = true) :
    ∃ index node, index.toNat = position ∧ tree.nodeAt index = some node ∧ protections.contains node.tag = true := by
  have member := List.contains_iff_mem.mp held
  revert member
  unfold_general_projection
  intro member
  obtain ⟨⟨index,node⟩,entry,found⟩ := List.mem_filterMap.mp member
  dsimp only at found
  split at found
  next heldTag =>
    exact ⟨index,node,Option.some.inj found,(GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mp entry,heldTag⟩
  next => cases found

/-- Raw path containment and absence of the escaping node tags form RestoreTo.
No ownership or operation-success result is an input. -/
theorem from_paths (tree : BorrowTree) (before after : ProtectedTags) (child target : UniIndex)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (subset : ∀ location : LocationTree,
      ∀ position ∈ (source_normal_projection tree location before).topology.ancestorPath target.toNat,
        position ∈ (source_normal_projection tree location before).topology.ancestorPath child.toNat)
    (escapingUnheld : ∀ (location : LocationTree) (index : UniIndex) (node : TreeNode), tree.nodeAt index = some node →
      index.toNat ∈ (source_normal_projection tree location before).topology.ancestorPath child.toNat →
      index.toNat ∉ (source_normal_projection tree location before).topology.ancestorPath target.toNat →
      after.contains node.tag = false) :
    GeneralBorrowFreshLifetimeRestore.RestoreTo tree before after child target (fun _ => true) := by
  refine ⟨GeneralBorrowNodeUpdate.lookup_valid tree.nodes target targetNode targetPresent,?_,?_⟩
  · intro location position localTarget
    have member : position ∈ (source_normal_projection tree location before).topology.ancestorPath target.toNat := by
      unfold GeneralBorrowAnchor.relation at localTarget
      split at localTarget
      next member => exact member
      next => cases localTarget
    refine ⟨?_,rfl⟩
    unfold GeneralBorrowAnchor.relation
    simp only [subset location position member,↓reduceIte]
  · intro location position localChild foreignTarget
    have member : position ∈ (source_normal_projection tree location before).topology.ancestorPath child.toNat := by
      unfold GeneralBorrowAnchor.relation at localChild
      split at localChild
      next member => exact member
      next => cases localChild
    have outside : position ∉ (source_normal_projection tree location before).topology.ancestorPath target.toNat := by
      intro included
      unfold GeneralBorrowAnchor.relation at foreignTarget
      simp only [included,↓reduceIte] at foreignTarget
      cases foreignTarget
    cases held : (source_normal_projection tree location after).protectedNodes.contains position with
    | false => rfl
    | true =>
      obtain ⟨index,node,equal,present,heldTag⟩ := protected_witness tree location after position held
      have unheld := escapingUnheld location index node present (by rw [equal];exact member) (by rw [equal];exact outside)
      rw [unheld] at heldTag
      cases heldTag

/-- The actual endCall fold removes registered escaping tags and retains
absence of all initially unprotected escaping tags. This discharges the post-
protector-table metadata from initial path/registration data. -/
theorem end_call (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (child target : UniIndex)
    (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (subset : ∀ location : LocationTree,
      ∀ position ∈ (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat,
        position ∈ (source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat)
    (escaping : ∀ (location : LocationTree) (index : UniIndex) (node : TreeNode), tree.nodeAt index = some node →
      index.toNat ∈ (source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat →
      index.toNat ∉ (source_normal_projection tree location global.protectedTags).topology.ancestorPath target.toNat →
      global.protectedTags.contains node.tag = false ∨ ∃ allocation : AllocId, (allocation,node.tag) ∈ frame.protectedTags.toList) :
    GeneralBorrowFreshLifetimeRestore.RestoreTo tree global.protectedTags (global.endCall frame).protectedTags child target (fun _ => true) := by
  apply from_paths tree global.protectedTags (global.endCall frame).protectedTags child target targetNode targetPresent subset
  intro location index node present localChild foreignTarget
  rcases escaping location index node present localChild foreignTarget with absent | ⟨allocation,registered⟩
  · have preserved := GeneralBorrowRelease.remove_fold_absent frame.protectedTags.toList global.protectedTags node.tag absent
    simpa only [GlobalState.endCall,Array.foldl_toList] using preserved
  · exact GeneralBorrowRelease.end_call_owned_absent global frame allocation node.tag registered
/-- Changing the source protection table does not change either ancestor path.
This aligns restored ownership with the actual post-endCall input table. -/
theorem before_context (tree : BorrowTree) (before replacement after : ProtectedTags)
    (child target : UniIndex) (data : GeneralBorrowFreshLifetimeRestore.RestoreTo tree before after child target (fun _ => true)) :
    GeneralBorrowFreshLifetimeRestore.RestoreTo tree replacement after child target (fun _ => true) :=
  ⟨data.targetValid,data.localRetained,data.leavingReleased⟩
end DuplicatePrefix.GeneralBorrowFreshRestoreData
