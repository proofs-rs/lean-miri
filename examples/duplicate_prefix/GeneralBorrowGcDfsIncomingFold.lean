import duplicate_prefix.GeneralBorrowGcDfsIncomingCollapse
import duplicate_prefix.GeneralBorrowGcDfsEligibilityShape

namespace DuplicatePrefix.GeneralBorrowGcDfsIncomingFold
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcDfsIncoming
open DuplicatePrefix.GeneralBorrowGcChildFold DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem removal_success (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) : (source_remove_useless_node tree index).2 = .ok () := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]

/-- The REAL callback preserves completed incoming backlinks and active child
coverage. Leaf/unary source eligibility supplies the exact outgoing shape;
atomic collapse repairs the sole temporary dangling replacement pointer. -/
theorem step (original seed tree : BorrowTree) (processed : List UniIndex) (root parent index : UniIndex)
    (live : Array BorTag) (kept : Array UniIndex) (rest : List UniIndex) (originalNode : TreeNode)
    (originalPresent : original.nodes.get index = some originalNode) (originalEdge : originalNode.parent = some parent)
    (completed : index ∈ processed) (pendingParent : parent ∉ processed)
    (data : GeneralBorrowGcDfsPendingFold.Data original processed parent tree)
    (incoming : Active original processed parent (index::rest) kept tree) :
    ∃ after result, childScan seed root live parent index (none,tree,kept) = .yield (none,after,result) ∧
      GeneralBorrowGcDfsPendingFold.Data original processed parent after ∧ Active original processed parent rest result after := by
  have dataAfter : ∀ after result, childScan seed root live parent index (none,tree,kept) = .yield (none,after,result) →
      GeneralBorrowGcDfsPendingFold.Data original processed parent after := by
    intro after result actual
    have preserved := GeneralBorrowGcDfsPendingFold.step original seed processed root parent index live originalNode
      originalPresent originalEdge completed pendingParent (none,tree,kept) ⟨data,by simp⟩
    rw [actual] at preserved
    exact preserved.1
  cases useless : gc_useless tree index live with
  | true =>
    obtain ⟨node,present,empty⟩ := GeneralBorrowGcDfsEligibilityShape.useless tree index live useless
    have success := removal_success tree index node present
    have actual : childScan seed root live parent index (none,tree,kept) = .yield (none,(source_remove_useless_node tree index).1,kept) := by
      cases removed : source_remove_useless_node tree index with
      | mk after outcome =>
        have ok : outcome = .ok () := by simpa only [removed] using success
        simp only [childScan,useless,↓reduceIte,removed,ok,pure]
    exact ⟨_,kept,actual,dataAfter _ _ actual,GeneralBorrowGcDfsIncomingRemove.leaf original tree processed parent index rest kept node present empty incoming⟩
  | false =>
    cases candidate : gc_replacement tree index live with
    | none =>
      have actual : childScan seed root live parent index (none,tree,kept) = .yield (none,tree,kept.push index) := by
        simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,pure]
      exact ⟨tree,kept.push index,actual,data,GeneralBorrowGcDfsIncoming.keep original tree processed parent index rest kept incoming⟩
    | some replacement =>
      obtain ⟨node,replacementNode,present,member,replacementPresent⟩ := GeneralBorrowGcEligibilityFacts.replacement_present tree index replacement live candidate
      obtain ⟨singleNode,singlePresent,single⟩ := GeneralBorrowGcDfsEligibilityShape.replacement tree index replacement live candidate
      have equal := Option.some.inj (present.symm.trans singlePresent)
      subst singleNode
      obtain ⟨value,valuePresent,valueParent⟩ := data.repaired.children index completed node present replacement member
      have equal := Option.some.inj (replacementPresent.symm.trans valuePresent)
      subst value
      have parentEq := (data.frame index originalNode originalPresent (.inr ⟨parent,originalEdge,pendingParent⟩) node present).1
      have different : replacement ≠ index := by
        intro same;subst replacement
        have equal := Option.some.inj (present.symm.trans replacementPresent)
        subst replacementNode
        have equal := Option.some.inj (valueParent.symm.trans (parentEq.trans originalEdge))
        exact pendingParent (equal ▸ completed)
      have afterPresent := (GeneralBorrowGcDfsIncomingRemove.other tree index replacement node present different).trans replacementPresent
      have success := removal_success tree index node present
      let after := GeneralBorrowGcDfsIncomingCollapse.collapsed tree index replacement parent replacementNode
      have actual : childScan seed root live parent index (none,tree,kept) = .yield (none,after,kept.push replacement) := by
        cases removed : source_remove_useless_node tree index with
        | mk current outcome =>
          have ok : outcome = .ok () := by simpa only [removed] using success
          have retained : current.nodes.get replacement = some replacementNode := by simpa only [removed] using afterPresent
          simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,after,GeneralBorrowGcDfsIncomingCollapse.collapsed,removed,ok,retained,pure]
      exact ⟨after,kept.push replacement,actual,dataAfter _ _ actual,
        GeneralBorrowGcDfsIncomingCollapse.preserves original tree processed parent index replacement rest kept node replacementNode
          present single replacementPresent different pendingParent incoming⟩

/-- Source child-fold completion and incoming-edge preservation are derived
jointly from static original edges and the genuine incoming/pending stages. -/
theorem fold (original seed tree : BorrowTree) (processed : List UniIndex) (root parent : UniIndex)
    (live : Array BorTag) (items : List UniIndex) (kept : Array UniIndex)
    (originalChildren : ∀ index ∈ items, ∃ node, original.nodes.get index = some node ∧ node.parent = some parent)
    (completed : ∀ index ∈ items, index ∈ processed) (pendingParent : parent ∉ processed)
    (data : GeneralBorrowGcDfsPendingFold.Data original processed parent tree)
    (incoming : Active original processed parent items kept tree) :
    ∃ after result, forIn (m := Id) items (none,tree,kept) (childScan seed root live parent) = (none,after,result) ∧
      GeneralBorrowGcDfsPendingFold.Data original processed parent after ∧ Active original processed parent [] result after := by
  induction items generalizing tree kept with
  | nil => exact ⟨tree,kept,rfl,data,incoming⟩
  | cons index rest ih =>
    obtain ⟨node,present,edge⟩ := originalChildren index (by simp)
    obtain ⟨middle,accumulated,actual,middleData,middleIncoming⟩ := step original seed tree processed root parent index live kept rest node present edge
      (completed index (by simp)) pendingParent data incoming
    obtain ⟨after,result,tail,finalData,finalIncoming⟩ := ih middle accumulated
      (fun child member => originalChildren child (List.mem_cons_of_mem _ member))
      (fun child member => completed child (List.mem_cons_of_mem _ member)) middleData middleIncoming
    refine ⟨after,result,?_,finalData,finalIncoming⟩
    rw [List.forIn_cons,actual]
    simpa only [bind] using tail

end DuplicatePrefix.GeneralBorrowGcDfsIncomingFold
