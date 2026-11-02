import duplicate_prefix.GeneralBorrowEffectfulRetagReady
import duplicate_prefix.GeneralBorrowEffectfulTreeUpdateFrame
namespace DuplicatePrefix.GeneralBorrowEffectfulRetagReadyFormation
open Miri Miri.Memory Miri.ABI Miri.TreeBorrows
open GeneralBorrowWildcardParentTagOrder GeneralBorrowEffectfulTreeUpdateFrame GeneralBorrowEffectfulRetagCausalOrder
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
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

/-- Build the internal actual-retag loop packet from ORIGINAL allocation data.
It is not a proposed Valid contract. In particular no successful access, child
constructor, retag or function call is an input. -/
theorem forms {K : Type} (memory : MemoryState Provenance BorrowTree K) (global : GlobalState)
    (unique : (memory.live.toList.map Prod.fst).Nodup)
    (runtime : ∀ row ∈ memory.live.toList, DuplicatePrefixBorrowContract.RuntimeFacts row.2.allocation.extra global)
    (orders : AllTrees (fun _ tree => ParentTagOrder tree) memory)
    (room : ∀ row ∈ memory.live.toList, row.2.allocation.extra.nodes.size+1 ≤ 4294967295)
    (target : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == target) = some (target,entry))
    (parentTag : BorTag) (parent : UniIndex) (node : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag = some parent)
    (nodePresent : entry.allocation.extra.nodeAt parent = some node) :
    AllTrees (Ready global.nextPointerTag parentTag target) memory := by
  intro row live
  have formed := runtime row live
  obtain ⟨mapping,index,inserted,_,vacant,_⟩ := GeneralBorrowWildcardConstructorSlot.select row.2.allocation.extra global formed
    global.nextPointerTag (GeneralBorrowParentTagInvariant.fresh _ _ formed) (room row live) .Disabled .None
  refine ⟨orders row live,⟨GeneralBorrowStructuralHistoryShared.depth _ formed.formed.toState⟩,
    ⟨mapping,index,inserted,vacant⟩,?_,?_⟩
  · intro index node found
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp
      (GeneralBorrowParentTagInvariant.parent_below_fresh _ _ formed index node found)))
  · intro key
    have member : (target,entry) ∈ memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some present)
    have equal : row = (target,entry) := same_key _ unique _ _ live member key
    subst row
    exact ⟨parent,node,tagged,nodePresent⟩
end DuplicatePrefix.GeneralBorrowEffectfulRetagReadyFormation
