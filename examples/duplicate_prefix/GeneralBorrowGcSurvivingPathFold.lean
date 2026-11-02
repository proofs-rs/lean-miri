import duplicate_prefix.GeneralBorrowGcSurvivingPaths
import duplicate_prefix.GeneralBorrowGcDfsIncomingFold

namespace DuplicatePrefix.GeneralBorrowGcSurvivingPathFold
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcChildFold DuplicatePrefix.GeneralBorrowGcGuardedFold
open DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- The actual source callback preserves exact surviving ancestry, using raw
completed incoming/outgoing graph facts for leaf and unary eligibility. -/
theorem step (original seed tree : BorrowTree) (processed : List UniIndex) (root parent index : UniIndex)
    (live : Array BorTag) (kept : Array UniIndex) (rest : List UniIndex) (originalNode : TreeNode)
    (originalPresent : original.nodes.get index = some originalNode) (originalEdge : originalNode.parent = some parent)
    (completed : index ∈ processed) (pendingParent : parent ∉ processed)
    (data : GeneralBorrowGcDfsPendingFold.Data original processed parent tree)
    (incoming : Active original processed parent (index::rest) kept tree)
    (paths : GeneralBorrowGcSurvivingPaths.Valid original.nodes tree.nodes) :
    ∃ after result, childScan seed root live parent index (none,tree,kept) = .yield (none,after,result) ∧
      GeneralBorrowGcDfsPendingFold.Data original processed parent after ∧
      Active original processed parent rest result after ∧ GeneralBorrowGcSurvivingPaths.Valid original.nodes after.nodes := by
  obtain ⟨after,result,actual,finalData,finalIncoming⟩ := GeneralBorrowGcDfsIncomingFold.step original seed tree processed
    root parent index live kept rest originalNode originalPresent originalEdge completed pendingParent data incoming
  refine ⟨after,result,actual,finalData,finalIncoming,?_⟩
  cases useless : gc_useless tree index live with
  | true =>
    obtain ⟨node,present,empty⟩ := GeneralBorrowGcDfsEligibilityShape.useless tree index live useless
    have leaf : ∀ query value,tree.nodes.get query = some value → value.parent ≠ some index := by
      intro query value found edge
      obtain ⟨actualNode,actualFound,member⟩ := incoming.completed query value found index edge completed
      have same := Option.some.inj (present.symm.trans actualFound)
      subst actualNode
      rw [empty] at member
      cases member
    have contracted := GeneralBorrowGcSurvivingPaths.contract original.nodes tree.nodes (tree.nodes.remove index) index node
      (GeneralBorrowGcCacheAtomic.leaf_contract tree.nodes index node present leaf) paths
    have success : (source_remove_useless_node tree index).2 = .ok () := (GeneralBorrowFreshDeassignment.removed_clean tree index node present).1
    have predicted : childScan seed root live parent index (none,tree,kept) =
        .yield (none,(source_remove_useless_node tree index).1,kept) := by
      cases removed : source_remove_useless_node tree index with
      | mk current outcome =>
        have ok : outcome = .ok () := by simpa only [removed] using success
        simp only [childScan,useless,↓reduceIte,removed,ok,pure]
    have same := congrArg (fun state : ForInStep DuplicatePrefix.GeneralBorrowGcWalker.ChildState => state.value.2.1) (actual.symm.trans predicted)
    change after = (source_remove_useless_node tree index).1 at same
    rw [same]
    unfold_source_remove_useless_node
    simpa only [present,Id.run,pure] using contracted
  | false =>
    cases candidate : gc_replacement tree index live with
    | none =>
      have predicted : childScan seed root live parent index (none,tree,kept) = .yield (none,tree,kept.push index) := by
        simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,pure]
      have same := congrArg (fun state : ForInStep DuplicatePrefix.GeneralBorrowGcWalker.ChildState => state.value.2.1) (actual.symm.trans predicted)
      change after = tree at same
      rw [same]
      exact paths
    | some replacement =>
      obtain ⟨node,replacementNode,present,member,replacementPresent⟩ := GeneralBorrowGcEligibilityFacts.replacement_present tree index replacement live candidate
      obtain ⟨singleNode,singlePresent,single⟩ := GeneralBorrowGcDfsEligibilityShape.replacement tree index replacement live candidate
      have equal := Option.some.inj (present.symm.trans singlePresent)
      subst singleNode
      obtain ⟨value,valuePresent,valueParent⟩ := data.repaired.children index completed node present replacement member
      have equal := Option.some.inj (replacementPresent.symm.trans valuePresent)
      subst value
      have parentEq := (data.frame index originalNode originalPresent (.inr ⟨parent,originalEdge,pendingParent⟩) node present).1.trans originalEdge
      have different : replacement ≠ index := by
        intro same;subst replacement
        have equal := Option.some.inj (present.symm.trans replacementPresent)
        subst replacementNode
        have equal := Option.some.inj (valueParent.symm.trans parentEq)
        exact pendingParent (equal ▸ completed)
      have unique : ∀ query value,tree.nodes.get query = some value → value.parent = some index → query = replacement := by
        intro query value found edge
        obtain ⟨actualNode,actualFound,member⟩ := incoming.completed query value found index edge completed
        have same := Option.some.inj (present.symm.trans actualFound)
        subst actualNode
        rw [single] at member
        exact List.mem_singleton.mp member
      have contracted := GeneralBorrowGcSurvivingPaths.contract original.nodes tree.nodes _ index node
        (GeneralBorrowGcCacheAtomic.collapse_contract tree.nodes index replacement node replacementNode present replacementPresent different valueParent unique) paths
      let middle := GeneralBorrowGcDfsIncomingCollapse.collapsed tree index replacement parent replacementNode
      have retained := (GeneralBorrowGcDfsIncomingRemove.other tree index replacement node present different).trans replacementPresent
      have success : (source_remove_useless_node tree index).2 = .ok () := (GeneralBorrowFreshDeassignment.removed_clean tree index node present).1
      have predicted : childScan seed root live parent index (none,tree,kept) = .yield (none,middle,kept.push replacement) := by
        cases removed : source_remove_useless_node tree index with
        | mk current outcome =>
          have ok : outcome = .ok () := by simpa only [removed] using success
          have nextPresent : current.nodes.get replacement = some replacementNode := by simpa only [removed] using retained
          simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,middle,GeneralBorrowGcDfsIncomingCollapse.collapsed,removed,ok,nextPresent,pure]
      have same := congrArg (fun state : ForInStep DuplicatePrefix.GeneralBorrowGcWalker.ChildState => state.value.2.1) (actual.symm.trans predicted)
      change after = middle at same
      rw [same]
      dsimp only [middle,GeneralBorrowGcDfsIncomingCollapse.collapsed]
      unfold_source_remove_useless_node
      simpa only [present,Id.run,pure,GeneralBorrowGcCacheAtomic.collapsed,parentEq] using contracted

/-- All actual callbacks compose their exact ancestry equivalences; successful
source outcomes, next graph stages and path facts are derived together. -/
theorem fold (original seed tree : BorrowTree) (processed : List UniIndex) (root parent : UniIndex)
    (live : Array BorTag) (items : List UniIndex) (kept : Array UniIndex)
    (originalChildren : ∀ index ∈ items, ∃ node, original.nodes.get index = some node ∧ node.parent = some parent)
    (completed : ∀ index ∈ items,index ∈ processed) (pendingParent : parent ∉ processed)
    (data : GeneralBorrowGcDfsPendingFold.Data original processed parent tree)
    (incoming : Active original processed parent items kept tree)
    (paths : GeneralBorrowGcSurvivingPaths.Valid original.nodes tree.nodes) :
    ∃ after result,forIn (m := Id) items (none,tree,kept) (childScan seed root live parent) = (none,after,result) ∧
      GeneralBorrowGcDfsPendingFold.Data original processed parent after ∧ Active original processed parent [] result after ∧
      GeneralBorrowGcSurvivingPaths.Valid original.nodes after.nodes := by
  induction items generalizing tree kept with
  | nil => exact ⟨tree,kept,rfl,data,incoming,paths⟩
  | cons index rest ih =>
    obtain ⟨node,present,edge⟩ := originalChildren index (by simp)
    obtain ⟨middle,accumulated,actual,middleData,middleIncoming,middlePaths⟩ := step original seed tree processed root parent index live kept rest node present edge
      (completed index (by simp)) pendingParent data incoming paths
    obtain ⟨after,result,tail,finalData,finalIncoming,finalPaths⟩ := ih middle accumulated
      (fun child member => originalChildren child (List.mem_cons_of_mem _ member))
      (fun child member => completed child (List.mem_cons_of_mem _ member)) middleData middleIncoming middlePaths
    refine ⟨after,result,?_,finalData,finalIncoming,finalPaths⟩
    rw [List.forIn_cons,actual]
    simpa only [bind] using tail

end DuplicatePrefix.GeneralBorrowGcSurvivingPathFold
