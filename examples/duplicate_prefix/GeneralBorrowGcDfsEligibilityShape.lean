import duplicate_prefix.GeneralBorrowGcEligibilityFacts

namespace DuplicatePrefix.GeneralBorrowGcDfsEligibilityShape
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcGuardedFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The actual dead-node branch deletes only a node with no outgoing children. -/
theorem useless (tree : BorrowTree) (index : UniIndex) (live : Array BorTag)
    (found : gc_useless tree index live = true) : ∃ node, tree.nodes.get index = some node ∧ node.children = #[] := by
  obtain ⟨node,present⟩ := GeneralBorrowGcEligibilityFacts.useless_present tree index live found
  refine ⟨node,present,?_⟩
  revert found
  unfold_gc_live_rules
  intro found
  simp only [present,Bool.and_eq_true] at found
  exact Array.isEmpty_iff.mp found.1

/-- The actual collapse branch has EXACTLY the returned child. Combined with
completed incoming backlinks this rules out all other dangling child pointers. -/
theorem replacement (tree : BorrowTree) (index candidate : UniIndex) (live : Array BorTag)
    (found : gc_replacement tree index live = some candidate) :
    ∃ node, tree.nodes.get index = some node ∧ node.children.toList = [candidate] := by
  obtain ⟨node,present,member⟩ := GeneralBorrowGcReplacementMember.member tree index candidate live found
  have one : node.children.size = 1 := by
    by_cases one : node.children.size = 1
    · exact one
    · have impossible : gc_replacement tree index live = none := by
        unfold_gc_live_rules
        simp [present,one,Id.run,pure]
      rw [impossible] at found
      cases found
  obtain ⟨child,single⟩ := Array.size_eq_one_iff.mp one
  rw [single] at member
  have same : candidate = child := by simpa using member
  exact ⟨node,present,by rw [single,same]⟩

end DuplicatePrefix.GeneralBorrowGcDfsEligibilityShape
