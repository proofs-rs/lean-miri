import duplicate_prefix.GeneralBorrowGcDfsPendingFold
import duplicate_prefix.GeneralBorrowGcDfsRankedPostvisit

namespace DuplicatePrefix.GeneralBorrowGcDfsPendingPostvisit
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A real source postvisit retains every original node whose parent is still
pending, with its original parent and tag, including all original roots. Actual
child callbacks derive this from original edges and repaired completed children.
The strengthened pending invariant is joined to the actual successful step,
ordinary Stage, strict ranks and capacity; no callback success is assumed. -/
theorem step (rank : UniIndex → Nat) (original seed tree : BorrowTree) (processed : List UniIndex)
    (root index : UniIndex) (node : TreeNode) (live : Array BorTag)
    (stack : Array (UniIndex × Nat)) (cursor steps : Nat)
    (stage : Stage original processed tree) (ranked : Ranked rank tree) (unprocessed : index ∉ processed)
    (present : original.nodes.get index = some node) (finished : ¬ cursor < node.children.size)
    (children : ∀ child ∈ node.children.toList, child ∈ processed)
    (originalEdges : ∀ child ∈ node.children.toList, ∃ childNode,
      original.nodes.get child = some childNode ∧ childNode.parent = some index)
    (pending : Pending original processed tree)
    (repaired : GeneralBorrowGcDfsReciprocalStage.Reciprocal processed tree)
    (budget : steps+1 ≤ tree.nodes.size*2+1) :
    ∃ after, outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
        .yield (none,after,stack,steps+1) ∧ Stage original (index::processed) after ∧
      Ranked rank after ∧ Pending original (index::processed) after ∧ after.nodes.size = tree.nodes.size := by
  have currentPresent := (stage.outside index unprocessed).trans present
  obtain ⟨middle,kept,actual,middleRank,keptRank,capacity⟩ := GeneralBorrowGcRankedChildFold.complete
    rank node.children.toList seed tree root index live #[] ranked
    (ranked index node currentPresent) (by simp)
  have staged := GeneralBorrowGcDfsChildStage.fold original seed processed node.children.toList root index live children
    (none,tree,#[]) ⟨stage,by simp,by simp⟩
  rw [actual] at staged
  have afterPresent := (staged.1.outside index unprocessed).trans present
  have initialData := GeneralBorrowGcDfsPendingFold.initial original tree processed index pending repaired
  have foldedData := GeneralBorrowGcDfsPendingFold.fold original seed processed root index live node.children
    originalEdges children unprocessed (none,tree,#[]) ⟨initialData,by simp⟩
  rw [←Array.forIn_toList,actual] at foldedData
  have retained := GeneralBorrowGcDfsPending.finish original middle (index::processed) index node afterPresent kept foldedData.1.pending
  have equation := GeneralBorrowGcDfsControl.finish_equation seed tree root index node live stack cursor steps currentPresent finished budget
  rw [←Array.forIn_toList,actual] at equation
  change middle.nodes.get index = some node at afterPresent
  simp only [afterPresent] at equation
  refine ⟨_,equation,GeneralBorrowGcDfsStage.finish original middle processed index node afterPresent kept staged.2.1 staged.1,
    GeneralBorrowGcStrictChildren.finish rank middle index node afterPresent kept keptRank middleRank,retained,?_⟩
  exact (GeneralBorrowNodeUpdate.insert_existing_size middle.nodes index node _ afterPresent).trans capacity

end DuplicatePrefix.GeneralBorrowGcDfsPendingPostvisit
