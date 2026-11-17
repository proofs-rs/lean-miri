import duplicate_prefix.GeneralBorrowGcDfsClaims
import duplicate_prefix.GeneralBorrowGcDfsRankedPostvisit

namespace DuplicatePrefix.GeneralBorrowGcDfsReadyPostvisit
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A real postvisit derives kept representative presence, exact parent edges
and distinctness, then marks its parent repaired. Both Pending and completed
outgoing reciprocity are therefore inductive across actual postvisits. The
source child certificates contain only ORIGINAL graph data. -/
theorem step (rank : UniIndex → Nat) (original seed tree : BorrowTree) (processed : List UniIndex)
    (root index : UniIndex) (node : TreeNode) (live : Array BorTag)
    (stack : Array (UniIndex × Nat)) (cursor steps : Nat)
    (stage : Stage original processed tree) (ranked : Ranked rank tree) (unprocessed : index ∉ processed)
    (present : original.nodes.get index = some node) (finished : ¬ cursor < node.children.size)
    (children : ∀ child ∈ node.children.toList, child ∈ processed)
    (distinct : node.children.toList.Nodup)
    (originalEdges : ∀ child ∈ node.children.toList, ∃ childNode,
      original.nodes.get child = some childNode ∧ childNode.parent = some index)
    (pending : Pending original processed tree)
    (repaired : GeneralBorrowGcDfsReciprocalStage.Reciprocal processed tree)
    (budget : steps+1 ≤ tree.nodes.size*2+1) :
    ∃ after, outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
        .yield (none,after,stack,steps+1) ∧ Stage original (index::processed) after ∧
      Ranked rank after ∧ Pending original (index::processed) after ∧
      GeneralBorrowGcDfsReciprocalStage.Reciprocal (index::processed) after ∧ after.nodes.size = tree.nodes.size := by
  have currentPresent := (stage.outside index unprocessed).trans present
  obtain ⟨middle,kept,actual,middleRank,keptRank,capacity⟩ := GeneralBorrowGcRankedChildFold.complete
    rank node.children.toList seed tree root index live #[] ranked
    (ranked index node currentPresent) (by simp)
  have initialData := GeneralBorrowGcDfsPendingFold.initial original tree processed index pending repaired
  have initialClaims : GeneralBorrowGcDfsClaims.Claims tree index ([] ++ node.children.toList) := by
    intro child member
    have childMember : child ∈ node.children.toList := by simpa using member
    obtain ⟨childNode,childPresent,childEdge⟩ := originalEdges child childMember
    obtain ⟨current,found,parentEq,_⟩ := pending child childNode childPresent (.inr ⟨index,childEdge,unprocessed⟩)
    exact ⟨current,found,parentEq.trans childEdge⟩
  obtain ⟨other,result,claimsActual,finalData,finalDistinct,finalClaims⟩ := GeneralBorrowGcDfsClaims.fold original seed tree processed
    root index live node.children.toList #[] originalEdges children unprocessed initialData (by simpa using distinct) initialClaims
  have same : (none,middle,kept) = (none,other,result) := actual.symm.trans claimsActual
  have sameTree := congrArg (fun state : ChildState => state.2.1) same
  have sameKept := congrArg (fun state : ChildState => state.2.2) same
  change middle = other at sameTree
  change kept = result at sameKept
  subst other
  subst result
  have staged := GeneralBorrowGcDfsChildStage.fold original seed processed node.children.toList root index live children
    (none,tree,#[]) ⟨stage,by simp,by simp⟩
  rw [actual] at staged
  have afterPresent := (staged.1.outside index unprocessed).trans present
  have retained := GeneralBorrowGcDfsPending.finish original middle (index::processed) index node afterPresent kept finalData.pending
  have reciprocal := GeneralBorrowGcDfsReciprocalStage.finish middle processed index node afterPresent kept finalDistinct finalClaims finalData.repaired
  have equation := GeneralBorrowGcDfsControl.finish_equation seed tree root index node live stack cursor steps currentPresent finished budget
  rw [←Array.forIn_toList,actual] at equation
  change middle.nodes.get index = some node at afterPresent
  simp only [afterPresent] at equation
  refine ⟨_,equation,GeneralBorrowGcDfsStage.finish original middle processed index node afterPresent kept staged.2.1 staged.1,
    GeneralBorrowGcStrictChildren.finish rank middle index node afterPresent kept keptRank middleRank,retained,reciprocal,?_⟩
  exact (GeneralBorrowNodeUpdate.insert_existing_size middle.nodes index node _ afterPresent).trans capacity

end DuplicatePrefix.GeneralBorrowGcDfsReadyPostvisit
