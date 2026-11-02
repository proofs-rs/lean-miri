import duplicate_prefix.GeneralBorrowGcLiveNode

namespace DuplicatePrefix.GeneralBorrowGcReplacementMember
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The actual unary-collapse candidate is an existing direct child of the
removed node; its location-policy test cannot manufacture another index. -/
theorem member (tree : BorrowTree) (index replacement : UniIndex) (live : Array BorTag)
    (found : gc_replacement tree index live = some replacement) :
    ∃ node, tree.nodes.get index = some node ∧ replacement ∈ node.children.toList := by
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
            exact ⟨node,present,by simpa using Array.mem_of_getElem? selected⟩
          · cases found
        · cases found
      · cases found
  · cases found
end DuplicatePrefix.GeneralBorrowGcReplacementMember
