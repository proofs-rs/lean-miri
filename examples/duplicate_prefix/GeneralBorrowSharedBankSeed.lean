import duplicate_prefix.GeneralBorrowSharedBankState
import duplicate_prefix.GeneralBorrowRecursiveSharedGeneration

namespace DuplicatePrefix.GeneralBorrowSharedBankSeed
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowSharedBankState

/-- A checked allocation-derived partition supplies the initial root handle
and its Read ownership, without supplying a successful access. -/
def of_partition (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (state : GeneralBorrowPartitionState.State tree root capacity) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) : State root offset len := by
  let initial := GeneralBorrowRecursiveSharedGeneration.of_partition tree root capacity state offset len bounds
  exact {
    tree := tree, resources := initial.resources, handles := [root]
    present := by
      intro index member
      have same : index = root := List.mem_singleton.mp member
      subst index
      exact ⟨state.node,state.star.present⟩
    bounds := initial.bounds
    owned := by
      intro index member position valid positive before after
      have same : index = root := List.mem_singleton.mp member
      subst index
      exact (initial.owned position valid positive before after).1 }
end DuplicatePrefix.GeneralBorrowSharedBankSeed
