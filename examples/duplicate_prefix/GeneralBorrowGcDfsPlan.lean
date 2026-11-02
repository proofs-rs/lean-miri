import duplicate_prefix.GeneralBorrowGcDfsRankedPostvisit

namespace DuplicatePrefix.GeneralBorrowGcDfsPlan
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A finite postorder schedule contains only ORIGINAL graph metadata and
cursor/processed-set facts. It contains no interpreter outcome or successful
operation assumption. Child traversal follows the exact source order. -/
inductive Plan (original : BorrowTree) : Array (UniIndex × Nat) → List UniIndex → List UniIndex → Nat → Prop where
  | done (processed : List UniIndex) : Plan original #[] processed processed 0
  | down (stack : Array (UniIndex × Nat)) (index : UniIndex) (cursor : Nat) (node : TreeNode)
      (processed final : List UniIndex) (count : Nat)
      (present : original.nodes.get index = some node) (unprocessed : index ∉ processed)
      (inside : cursor < node.children.size)
      (tail : Plan original ((stack.push (index,cursor+1)).push (node.children[cursor],0)) processed final count) :
      Plan original (stack.push (index,cursor)) processed final (count+1)
  | up (stack : Array (UniIndex × Nat)) (index : UniIndex) (cursor : Nat) (node : TreeNode)
      (processed final : List UniIndex) (count : Nat)
      (present : original.nodes.get index = some node) (unprocessed : index ∉ processed)
      (finished : ¬ cursor < node.children.size)
      (children : ∀ child ∈ node.children.toList, child ∈ processed)
      (tail : Plan original stack (index::processed) final count) :
      Plan original (stack.push (index,cursor)) processed final (count+1)

/-- Original-metadata postorder plans execute in the REAL GC while loop.
Strict ranks derive every callback's success; staged data derive every node
lookup. Only a static sourcecounter budget is supplied, not operation success. -/
theorem execute (rank : UniIndex → Nat) (original seed : BorrowTree) (root : UniIndex) (live : Array BorTag)
    {stack : Array (UniIndex × Nat)} {processed final : List UniIndex} {count : Nat}
    (plan : Plan original stack processed final count) (tree : BorrowTree) (steps : Nat)
    (stage : Stage original processed tree) (ranked : Ranked rank tree)
    (budget : steps+count ≤ tree.nodes.size*2+1) :
    ∃ after, Lean.Loop.forIn {} (none,tree,stack,steps) (outerScan seed root live) =
        (none,after,#[],steps+count) ∧ Stage original final after ∧
      Ranked rank after ∧ after.nodes.size = tree.nodes.size := by
  induction plan generalizing tree steps with
  | done processed =>
    refine ⟨tree,?_,stage,ranked,rfl⟩
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [outerScan,pure,bind]
  | down stack index cursor node processed final count present unprocessed inside tail ih =>
    have lookup := (stage.outside index unprocessed).trans present
    have actual := GeneralBorrowGcDfsControl.descend seed tree root index node live stack cursor steps lookup inside (by omega)
    obtain ⟨after,execution,finalStage,finalRank,capacity⟩ := ih tree (steps+1) stage ranked (by omega)
    refine ⟨after,?_,finalStage,finalRank,capacity⟩
    rw [Lean.Loop.forIn_eq_of_monadTail,actual]
    simp only [bind]
    have arithmetic : steps+1+count = steps+(count+1) := by omega
    simpa only [arithmetic] using execution
  | up stack index cursor node processed final count present unprocessed finished children tail ih =>
    obtain ⟨middle,actual,middleStage,middleRank,middleCapacity⟩ := GeneralBorrowGcDfsRankedPostvisit.step
      rank original seed tree processed root index node live stack cursor steps stage ranked unprocessed present finished children (by omega)
    have laterBudget : steps+1+count ≤ middle.nodes.size*2+1 := by rw [middleCapacity];omega
    obtain ⟨after,execution,finalStage,finalRank,capacity⟩ := ih middle (steps+1) middleStage middleRank laterBudget
    refine ⟨after,?_,finalStage,finalRank,capacity.trans middleCapacity⟩
    rw [Lean.Loop.forIn_eq_of_monadTail,actual]
    simp only [bind]
    have arithmetic : steps+1+count = steps+(count+1) := by omega
    simpa only [arithmetic] using execution
end DuplicatePrefix.GeneralBorrowGcDfsPlan
