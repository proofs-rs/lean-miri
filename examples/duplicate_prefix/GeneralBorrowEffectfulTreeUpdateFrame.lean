import duplicate_prefix.RetagEntry
namespace DuplicatePrefix.GeneralBorrowEffectfulTreeUpdateFrame
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Allocation-local data invariant, independent of retag execution outcomes. -/
def AllTrees {K : Type} (P : AllocId → BorrowTree → Prop)
    (memory : MemoryState Provenance BorrowTree K) : Prop :=
  ∀ row ∈ memory.live.toList, P row.1 row.2.allocation.extra

theorem updated {K : Type} (P : AllocId → BorrowTree → Prop)
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (before : AllTrees P memory) (replacement : P id tree) :
    AllTrees P (RetagEntry.updatedMemory memory id entry tree) := by
  intro row member
  change row ∈ ((memory.live.filter fun old => old.1 != id).push
    (id,{entry with allocation:=entry.allocation.setExtra tree})).toList at member
  rw [Array.toList_push] at member
  rcases List.mem_append.mp member with old | new
  · rw [Array.toList_filter] at old
    exact before row (List.mem_filter.mp old).1
  · have equal := List.mem_singleton.mp new
    subst row
    exact replacement

/-- Local successful-update equation used INSIDE actual retag branch proofs.
It does not assume retag or the target function succeeds. No allocation-ID
uniqueness or future-state certificate is required. -/
theorem update_success {K : Type} [DecidableEq K] (P : AllocId → BorrowTree → Prop)
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId) (tree : BorrowTree)
    (before : AllTrees P memory) (replacement : P id tree)
    (next : MemoryState Provenance BorrowTree K)
    (success : entry_tree_update memory id tree = .ok next) : AllTrees P next := by
  cases found : memory.live.find? (fun row => row.1 == id) with
  | none =>
    have failed : entry_tree_update memory id tree = .error (.unavailable id) := by
      unfold_entry_helper ".updateTreeExtra"
      simp only [found]
      rfl
    rw [failed] at success
    cases success
  | some row =>
    have key : row.1 = id := by simpa only [beq_iff_eq] using Array.find?_some found
    rcases row with ⟨keyId,entry⟩
    dsimp only at key
    subst keyId
    rw [RetagEntry.update_tree_exact memory id entry tree found] at success
    cases success
    exact updated P memory id entry tree before replacement
end DuplicatePrefix.GeneralBorrowEffectfulTreeUpdateFrame
