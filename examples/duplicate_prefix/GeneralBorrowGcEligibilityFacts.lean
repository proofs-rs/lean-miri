import duplicate_prefix.GeneralBorrowGcReplacementMember

namespace DuplicatePrefix.GeneralBorrowGcEligibilityFacts
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

theorem useless_present (tree : BorrowTree) (index : UniIndex) (live : Array BorTag)
    (found : gc_useless tree index live = true) : ∃ node, tree.nodes.get index = some node := by
  revert found
  unfold_gc_live_rules
  intro found
  cases present : tree.nodes.get index with
  | none => simp only [present,Bool.false_eq_true] at found
  | some node => exact ⟨node,rfl⟩

theorem replacement_present (tree : BorrowTree) (index replacement : UniIndex) (live : Array BorTag)
    (found : gc_replacement tree index live = some replacement) :
    ∃ node child, tree.nodes.get index = some node ∧ replacement ∈ node.children.toList ∧ tree.nodes.get replacement = some child := by
  revert found
  unfold_gc_live_rules
  intro found
  simp only [Id.run,bind,pure] at found
  split at found
  · rename_i node present
    split at found
    · cases found
    · split at found
      · rename_i child selected
        split at found
        · rename_i childNode childPresent
          split at found
          · cases found
            exact ⟨node,childNode,present,by simpa using Array.mem_of_getElem? selected,childPresent⟩
          · cases found
        · cases found
      · cases found
  · cases found
end DuplicatePrefix.GeneralBorrowGcEligibilityFacts
