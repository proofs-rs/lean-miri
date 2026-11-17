import duplicate_prefix.GeneralBorrowObserverReadDirectParent

namespace DuplicatePrefix.GeneralBorrowObserverReadTwoParents
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowAnchor
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem paths (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (child parent : UniIndex) (node : TreeNode) (present : tree.nodeAt child = some node)
    (edge : node.parent = some parent) :
    (source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat =
      child.toNat :: (source_normal_projection tree location global.protectedTags).topology.ancestorPath parent.toNat := by
  obtain ⟨forest⟩ := runtime.formed.forest location global.protectedTags
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child node present
  have projectedEdge : (nodeData (source_normal_projection tree location global.protectedTags).topology child.toNat).parent = some parent.toNat := by
    change ((source_normal_projection tree location global.protectedTags).topology.nodes[child.toNat]?.getD ⟨none,[]⟩).parent = _
    rw [projection_topology_node tree location global.protectedTags child.toNat child node rfl present]
    simp only [edge,Option.map_some]
  have size : (source_normal_projection tree location global.protectedTags).topology.nodes.size = tree.nodes.data.size := by
    unfold_general_projection;unfold_general_topology;simp only [Array.size_map]
  have bounded : child.toNat < (source_normal_projection tree location global.protectedTags).topology.nodes.size := by rw [size];exact valid
  exact (GeneralBorrowDirectParentGeometry.paths _ forest child.toNat parent.toNat bounded (by
    simpa only [nodeData,Array.getElem?_eq_getElem bounded,Option.getD_some] using projectedEdge)).1

/-- The actual two-level helper ancestry supplies every observer Read guard.
Both temporary tags are virtually removed, while the actual Read retains its
real protector list. No guard, final permission or successful release is assumed. -/
theorem access (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (child temporary observer : UniIndex) (childNode temporaryNode : TreeNode)
    (childPresent : tree.nodeAt child = some childNode) (childEdge : childNode.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some observer)
    (childHidden : childNode.isExposed = false) (temporaryHidden : temporaryNode.isExposed = false)
    (sourceRead : DuplicatePrefixNormalKind.Capability tree location global.protectedTags child .Read)
    (observerBoth : DuplicatePrefixBorrowAuthorization.Normal tree location
      ((global.endCall (({} : FrameState).addProtector allocation childNode.tag)).endCall
        (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags observer)
    (mode : ChildrenVisitMode) :
    (tree.performNormalAccessAt location child .Read global.protectedTags mode).access.status = .Completed ∧
    (tree.performNormalAccessAt location child .Read global.protectedTags mode).outcome = .ok () ∧
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal tree
      (tree.performNormalAccessAt location child .Read global.protectedTags mode).location
      ((global.endCall (({} : FrameState).addProtector allocation childNode.tag)).endCall
        (({} : FrameState).addProtector allocation temporaryNode.tag)).protectedTags observer,
      next.component = observerBoth.component := by
  let first := global.endCall (({} : FrameState).addProtector allocation childNode.tag)
  let second := first.endCall (({} : FrameState).addProtector allocation temporaryNode.tag)
  obtain ⟨firstRuntime,childAbsent,firstOther⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree global runtime
    allocation childNode.tag child childNode childPresent rfl childHidden
  obtain ⟨secondRuntime,temporaryAbsent,secondOther⟩ := GeneralBorrowHiddenProtectorDropRuntime.end_call tree first firstRuntime
    allocation temporaryNode.tag temporary temporaryNode temporaryPresent rfl temporaryHidden
  have childAbsentAfter : second.protectedTags.contains childNode.tag = false := by
    cases held : second.protectedTags.contains childNode.tag with
    | false => rfl
    | true =>
      have earlier := GeneralBorrowRelease.end_call_weakens first _ childNode.tag held
      rw [childAbsent] at earlier
      contradiction
  have firstPath := paths tree location global runtime child temporary childNode childPresent childEdge
  have secondPath := paths tree location global runtime temporary observer temporaryNode temporaryPresent temporaryEdge
  have fullPath : (source_normal_projection tree location global.protectedTags).topology.ancestorPath child.toNat =
      child.toNat :: temporary.toNat :: (source_normal_projection tree location global.protectedTags).topology.ancestorPath observer.toNat := by
    rw [firstPath,secondPath]
  apply GeneralBorrowObserverReadWriteback.access tree location global.protectedTags second.protectedTags runtime.formed.toGraphState
    child observer childNode childPresent sourceRead observerBoth runtime.formed.fits mode
  · intro index included localObserver
    change relation (source_normal_projection tree location global.protectedTags) observer.toNat index = .LocalAccess at localObserver
    unfold relation at localObserver ⊢
    rw [fullPath]
    split at localObserver
    next member => simp only [List.mem_cons,member,or_true,ite_true]
    next => contradiction
  · intro index included foreignObserver localChild
    change relation (source_normal_projection tree location global.protectedTags) observer.toNat index = .ForeignAccess at foreignObserver
    have either : index = child.toNat ∨ index = temporary.toNat := by
      unfold relation at foreignObserver localChild
      rw [fullPath] at localChild
      split at foreignObserver
      next => contradiction
      next excluded =>
        split at localChild
        next member =>
          simp only [List.mem_cons] at member
          rcases member with childSame | temporarySame | observerPath
          · exact .inl childSame
          · exact .inr temporarySame
          · exact False.elim (excluded observerPath)
        next => contradiction
    rcases either with same | same
    · subst index
      rw [GeneralBorrowNormalPermissionMetadata.held tree location second.protectedTags child childNode childPresent]
      exact childAbsentAfter
    · subst index
      rw [GeneralBorrowNormalPermissionMetadata.held tree location second.protectedTags temporary temporaryNode temporaryPresent]
      exact temporaryAbsent
  · intro index included foreignChild
    have neither : index ≠ child.toNat ∧ index ≠ temporary.toNat := by
      constructor
      · intro same
        subst index
        simp only [relation,fullPath,List.mem_cons_self,ite_true] at foreignChild
        cases foreignChild
      · intro same
        subst index
        simp only [relation,fullPath,List.mem_cons,List.mem_cons_self,or_true,true_or,ite_true] at foreignChild
        cases foreignChild
    have one := GeneralBorrowObserverReadDirectParent.flags_other tree location global runtime child childNode childPresent
      first.protectedTags firstOther index neither.1
    have two := GeneralBorrowObserverReadDirectParent.flags_other tree location first firstRuntime temporary temporaryNode temporaryPresent
      second.protectedTags secondOther index neither.2
    exact (two.trans one).symm

end DuplicatePrefix.GeneralBorrowObserverReadTwoParents
