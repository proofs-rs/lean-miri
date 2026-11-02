import duplicate_prefix.GeneralBorrowGcDfsIncomingFold

namespace DuplicatePrefix.GeneralBorrowGcDfsIncomingPostvisit
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual successful source postvisits preserve BOTH directions of the staged
parent/child graph, pending-node survival and origins. The active parent's stale
array is repaired by the real final rewrite, with no poststate Forest premise. -/
theorem step (rank : UniIndex → Nat) (original seed tree : BorrowTree) (processed : List UniIndex)
    (root index : UniIndex) (node : TreeNode) (live : Array BorTag)
    (stack : Array (UniIndex × Nat)) (cursor steps : Nat)
    (stage : Stage original processed tree) (ranked : Ranked rank tree) (unprocessed : index ∉ processed)
    (present : original.nodes.get index = some node) (finished : ¬ cursor < node.children.size)
    (children : ∀ child ∈ node.children.toList, child ∈ processed)
    (distinct : node.children.toList.Nodup)
    (originalEdges : ∀ child ∈ node.children.toList, ∃ childNode,
      original.nodes.get child = some childNode ∧ childNode.parent = some index)
    (backlinks : Backlinks original) (pending : Pending original processed tree)
    (repaired : GeneralBorrowGcDfsReciprocalStage.Reciprocal processed tree)
    (incoming : Incoming original processed tree) (budget : steps+1 ≤ tree.nodes.size*2+1) :
    ∃ after, outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
        .yield (none,after,stack,steps+1) ∧ Stage original (index::processed) after ∧
      Ranked rank after ∧ Pending original (index::processed) after ∧
      GeneralBorrowGcDfsReciprocalStage.Reciprocal (index::processed) after ∧
      Incoming original (index::processed) after ∧ after.nodes.size = tree.nodes.size := by
  obtain ⟨after,actual,finalStage,finalRank,finalPending,finalRepaired,capacity⟩ := GeneralBorrowGcDfsReadyPostvisit.step
    rank original seed tree processed root index node live stack cursor steps stage ranked unprocessed present finished children
    distinct originalEdges pending repaired budget
  have currentPresent := (stage.outside index unprocessed).trans present
  have initialData := GeneralBorrowGcDfsPendingFold.initial original tree processed index pending repaired
  have initialIncoming := activate original tree processed index node present unprocessed backlinks incoming
  obtain ⟨middle,kept,folded,_,active⟩ := GeneralBorrowGcDfsIncomingFold.fold original seed tree processed root index live node.children.toList #[]
    originalEdges children unprocessed initialData initialIncoming
  have staged := GeneralBorrowGcDfsChildStage.fold original seed processed node.children.toList root index live children
    (none,tree,#[]) ⟨stage,by simp,by simp⟩
  rw [folded] at staged
  have afterPresent := (staged.1.outside index unprocessed).trans present
  have restored := finish original middle processed index node afterPresent kept unprocessed active
  have equation := GeneralBorrowGcDfsControl.finish_equation seed tree root index node live stack cursor steps currentPresent finished budget
  rw [←Array.forIn_toList,folded] at equation
  change middle.nodes.get index = some node at afterPresent
  simp only [afterPresent] at equation
  have same := congrArg ForInStep.value (actual.symm.trans equation)
  have sameTree := congrArg (fun state : OuterState => state.2.1) same
  change after = {middle with nodes := middle.nodes.insert index {node with children := kept}} at sameTree
  subst after
  exact ⟨_,actual,finalStage,finalRank,finalPending,finalRepaired,restored,capacity⟩

end DuplicatePrefix.GeneralBorrowGcDfsIncomingPostvisit
