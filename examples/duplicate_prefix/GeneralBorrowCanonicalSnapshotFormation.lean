import duplicate_prefix.GeneralBorrowCanonicalChildCausalFrame
namespace DuplicatePrefix.GeneralBorrowCanonicalSnapshotFormation
open Miri Miri.Memory Miri.TreeBorrows
open GeneralBorrowCausalGraphFormation GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowCanonicalChildCausalFrame
set_option autoImplicit false
private theorem same_key {A B : Type} [DecidableEq A] (rows : List (A × B))
    (unique : (rows.map Prod.fst).Nodup) (left right : A × B)
    (leftMem : left ∈ rows) (rightMem : right ∈ rows) (key : left.1 = right.1) : left = right := by
  induction rows with
  | nil => cases leftMem
  | cons head tail ih =>
    simp only [List.map_cons,List.nodup_cons] at unique
    simp only [List.mem_cons] at leftMem rightMem
    rcases leftMem with equal | leftMem
    · subst left
      rcases rightMem with equal | rightMem
      · exact equal.symm
      · exact False.elim (unique.1 (List.mem_map.mpr ⟨right,rightMem,key.symm⟩))
    · rcases rightMem with equal | rightMem
      · subst right
        exact False.elim (unique.1 (List.mem_map.mpr ⟨left,leftMem,key⟩))
      · exact ih unique.2 leftMem rightMem

/-- The saved-target packet is derived from initial graph formation and
ordinary unique live allocation IDs. It imposes no additional future-state or
operation-success condition. General valid-state graph formation remains open. -/
theorem forms {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (unique : (memory.live.toList.map Prod.fst).Nodup)
    (before : AllTrees (fun _ tree => Formed tree) memory)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    AllTrees (Snapshot id entry.allocation.extra) memory := by
  intro row member
  refine ⟨before row member,?_⟩
  intro key
  have original : (id,entry) ∈ memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present)
  have equal := same_key memory.live.toList unique row (id,entry) member original key
  subst row
  exact ⟨rfl,rfl⟩
end DuplicatePrefix.GeneralBorrowCanonicalSnapshotFormation
