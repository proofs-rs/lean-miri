import duplicate_prefix.GeneralBorrowObserverReadWriteback
import duplicate_prefix.GeneralBorrowDirectParentGeometry
import duplicate_prefix.GeneralBorrowHiddenProtectorDropRuntime

namespace DuplicatePrefix.GeneralBorrowObserverReadDirectParent
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowAnchor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Projection protection bits change only at the unique node of the removed
fresh child tag. The runtime allocator supplies tag uniqueness. -/
theorem flags_other (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (child : UniIndex) (node : TreeNode) (present : tree.nodeAt child = some node)
    (after : ProtectedTags) (other : ∀ tag, tag ≠ node.tag → after.get tag = global.protectedTags.get tag)
    (query : Nat) (different : query ≠ child.toNat) :
    (source_normal_projection tree location after).protectedNodes.contains query =
      (source_normal_projection tree location global.protectedTags).protectedNodes.contains query := by
  have equivalent : (source_normal_projection tree location after).protectedNodes.contains query = true ↔
      (source_normal_projection tree location global.protectedTags).protectedNodes.contains query = true := by
    unfold_general_projection
    simp only [List.contains_iff_mem,List.mem_filterMap]
    constructor
    all_goals
      rintro ⟨⟨index,value⟩,member,selected⟩
      have lookup := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes index value).mp (by simpa using member)
      have differentTag : value.tag ≠ node.tag := by
        intro same
        have first := runtime.formed.allocator.nodeTags index value lookup
        have second := runtime.formed.allocator.nodeTags child node present
        rw [same,second] at first
        have equal := Option.some.inj first
        subst index
        split at selected
        next held => exact different (Option.some.inj selected).symm
        next => contradiction
      have equal : after.contains value.tag = global.protectedTags.contains value.tag := by
        unfold ProtectedTags.contains
        rw [other value.tag differentTag]
      exact ⟨(index,value),member,by simpa only [equal] using selected⟩
  cases left : (source_normal_projection tree location after).protectedNodes.contains query <;>
    cases right : (source_normal_projection tree location global.protectedTags).protectedNodes.contains query
  · rfl
  · exact False.elim (Bool.noConfusion ((equivalent.mpr right).symm.trans left))
  · exact False.elim (Bool.noConfusion ((equivalent.mp left).symm.trans right))
  · rfl

/-- A normal Read through an actual direct shared child preserves the mutable
parent's independent Both table with that fresh protector virtually erased.
The three visitor guards are derived from the actual parent edge, runtime tag
uniqueness and singleton endCall, rather than supplied as future capabilities. -/
theorem access (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (child parent : UniIndex) (node : TreeNode)
    (present : tree.nodeAt child = some node) (edge : node.parent = some parent)
    (hidden : node.isExposed = false)
    (sourceRead : DuplicatePrefixNormalKind.Capability tree location global.protectedTags child .Read)
    (observerBoth : DuplicatePrefixBorrowAuthorization.Normal tree location
      (global.endCall (({} : FrameState).addProtector allocation node.tag)).protectedTags parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt location child .Read global.protectedTags mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location child .Read global.protectedTags mode).outcome = .ok () ∧
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location child .Read global.protectedTags mode).location
      (global.endCall (({} : FrameState).addProtector allocation node.tag)).protectedTags parent,
      next.component = observerBoth.component := by
  let after := (global.endCall (({} : FrameState).addProtector allocation node.tag)).protectedTags
  obtain ⟨_,absent,other⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree global runtime
    allocation node.tag child node present rfl hidden
  obtain ⟨forest⟩ := runtime.formed.toGraphState.forest location global.protectedTags
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child node present
  have projectedEdge : (nodeData (source_normal_projection tree location global.protectedTags).topology child.toNat).parent = some parent.toNat := by
    change ((source_normal_projection tree location global.protectedTags).topology.nodes[child.toNat]?.getD ⟨none,[]⟩).parent = _
    rw [projection_topology_node tree location global.protectedTags child.toNat child node rfl present]
    simp only [edge,Option.map_some]
  have size : (source_normal_projection tree location global.protectedTags).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have bounded : child.toNat < (source_normal_projection tree location global.protectedTags).topology.nodes.size := by rw [size];exact valid
  have paths := GeneralBorrowDirectParentGeometry.paths _ forest child.toNat parent.toNat bounded (by
    simpa only [nodeData,Array.getElem?_eq_getElem bounded,Option.getD_some] using projectedEdge)
  apply GeneralBorrowObserverReadWriteback.access tree location global.protectedTags after runtime.formed.toGraphState
    child parent node present sourceRead observerBoth fits mode
  · intro index included localParent
    change relation (source_normal_projection tree location global.protectedTags) parent.toNat index = .LocalAccess at localParent
    unfold relation at localParent ⊢
    rw [paths.1]
    split at localParent
    next member => simp only [List.mem_cons,member,or_true,ite_true]
    next => contradiction
  · intro index included foreignParent localChild
    have same : index = child.toNat := by
      change relation (source_normal_projection tree location global.protectedTags) parent.toNat index = .ForeignAccess at foreignParent
      unfold relation at foreignParent localChild
      rw [paths.1] at localChild
      split at foreignParent
      next => contradiction
      next excluded =>
        split at localChild
        next member => exact (List.mem_cons.mp member).resolve_right excluded
        next => contradiction
    subst index
    rw [GeneralBorrowNormalPermissionMetadata.held tree location after child node present]
    exact absent
  · intro index included foreignChild
    have different : index ≠ child.toNat := by
      intro same
      subst index
      simp only [relation,paths.1,List.mem_cons_self,ite_true] at foreignChild
      cases foreignChild
    exact (flags_other tree location global runtime child node present after other index different).symm

end DuplicatePrefix.GeneralBorrowObserverReadDirectParent
