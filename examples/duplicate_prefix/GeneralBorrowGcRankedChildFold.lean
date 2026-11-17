import duplicate_prefix.GeneralBorrowGcStrictChildren
import duplicate_prefix.GeneralBorrowGcEligibilityFacts

namespace DuplicatePrefix.GeneralBorrowGcRankedChildFold
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold DuplicatePrefix.GeneralBorrowGcGuardedFold
open DuplicatePrefix.GeneralBorrowGcStrictChildren
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem remove_success (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (source_remove_useless_node tree index).2 = .ok () := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]

private theorem remove_other (tree : BorrowTree) (index query : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (different : query ≠ index) :
    (source_remove_useless_node tree index).1.nodes.get query = tree.nodes.get query := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowSparseRemoval.remove_get_other tree.nodes index query different

private theorem remove_size (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    (source_remove_useless_node tree index).1.nodes.size = tree.nodes.size := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,pure]
  exact GeneralBorrowSparseRemoval.remove_size tree.nodes index

/-- Strict child ranks exclude self replacement, so every actual child callback
completes. Even its deletion and collapse branches derive success from data.
Kept representatives retain strict rank above the suspended parent. -/
theorem step (rank : UniIndex → Nat) (seed tree : BorrowTree) (root parent index : UniIndex)
    (live : Array BorTag) (kept : Array UniIndex) (ranked : Ranked rank tree)
    (above : rank parent < rank index) (keptAbove : ∀ child ∈ kept.toList, rank parent < rank child) :
    ∃ after result, childScan seed root live parent index (none,tree,kept) = .yield (none,after,result) ∧
      Ranked rank after ∧ (∀ child ∈ result.toList, rank parent < rank child) ∧ after.nodes.size = tree.nodes.size := by
  cases useless : gc_useless tree index live with
  | true =>
    obtain ⟨node,present⟩ := GeneralBorrowGcEligibilityFacts.useless_present tree index live useless
    have removal := remove_success tree index node present
    refine ⟨(source_remove_useless_node tree index).1,kept,?_,remove rank tree index ranked,keptAbove,remove_size tree index node present⟩
    cases actual : source_remove_useless_node tree index with
    | mk after outcome =>
      have ok : outcome = .ok () := by simpa only [actual] using removal
      simp only [childScan,useless,↓reduceIte,actual,ok,pure]
  | false =>
    cases candidate : gc_replacement tree index live with
    | none =>
      refine ⟨tree,kept.push index,?_,ranked,?_,rfl⟩
      · simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,pure]
      · intro child member
        rcases Array.mem_push.mp (by simpa using member) with old | same
        · exact keptAbove child (by simpa using old)
        · simpa only [same] using above
    | some replacement =>
      obtain ⟨node,replacementNode,present,member,replacementPresent⟩ := GeneralBorrowGcEligibilityFacts.replacement_present tree index replacement live candidate
      have larger := ranked index node present replacement member
      have different : replacement ≠ index := by intro same;rw [same] at larger;omega
      have removal := remove_success tree index node present
      have replacementAfter := (remove_other tree index replacement node present different).trans replacementPresent
      let after := {(source_remove_useless_node tree index).1 with
        nodes := (source_remove_useless_node tree index).1.nodes.insert replacement {replacementNode with parent := some parent}}
      refine ⟨after,kept.push replacement,?_,reparent rank _ replacement parent replacementNode replacementAfter (remove rank tree index ranked),?_,?_⟩
      · cases actual : source_remove_useless_node tree index with
        | mk removed outcome =>
          have ok : outcome = .ok () := by simpa only [actual] using removal
          have retained : removed.nodes.get replacement = some replacementNode := by simpa only [actual] using replacementAfter
          simp only [childScan,useless,Bool.false_eq_true,↓reduceIte,candidate,after,actual,ok,retained,pure]
      · intro child member
        rcases Array.mem_push.mp (by simpa using member) with old | same
        · exact keptAbove child (by simpa using old)
        · have bound := Nat.lt_trans above larger
          simpa only [same] using bound
      · exact (GeneralBorrowNodeUpdate.insert_existing_size _ replacement replacementNode _ replacementAfter).trans (remove_size tree index node present)
/-- The exact source child fold completes at arbitrary subtree depth under
strict child ranks, retaining capacity and ranked kept representatives. No
child-fold outcome or operation-success condition is an input. -/
theorem complete (rank : UniIndex → Nat) (items : List UniIndex) (seed tree : BorrowTree)
    (root parent : UniIndex) (live : Array BorTag) (kept : Array UniIndex)
    (ranked : Ranked rank tree) (above : ∀ child ∈ items, rank parent < rank child)
    (keptAbove : ∀ child ∈ kept.toList, rank parent < rank child) :
    ∃ after result, forIn (m := Id) items (none,tree,kept) (childScan seed root live parent) = (none,after,result) ∧
      Ranked rank after ∧ (∀ child ∈ result.toList, rank parent < rank child) ∧ after.nodes.size = tree.nodes.size := by
  induction items generalizing tree kept with
  | nil => exact ⟨tree,kept,rfl,ranked,keptAbove,rfl⟩
  | cons index rest ih =>
    obtain ⟨middle,accumulated,actual,middleRank,partialRank,capacity⟩ := step rank seed tree root parent index live kept ranked
      (above index (by simp)) keptAbove
    obtain ⟨after,result,tail,finalRank,resultRank,finalCapacity⟩ := ih middle accumulated middleRank
      (fun child member => above child (List.mem_cons_of_mem _ member)) partialRank
    refine ⟨after,result,?_,finalRank,resultRank,finalCapacity.trans capacity⟩
    rw [List.forIn_cons,actual]
    simpa only [bind] using tail
end DuplicatePrefix.GeneralBorrowGcRankedChildFold
