import duplicate_prefix.GeneralBorrowGcWhileInvariant
import duplicate_prefix.GeneralBorrowGcRootInvariant
namespace DuplicatePrefix.GeneralBorrowGcAllocatorFull
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcAllocator
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- Allocator history data ignore location normalization, permissions and
exposure caches. This transport makes no claim about those other invariants. -/
theorem locations_preserves (tree : BorrowTree) (locations : Miri.DataStructures.DedupRangeMap LocationTree)
    (initial : Invariant tree) : Invariant {tree with locations := locations} :=
  ⟨initial.pool,initial.accounting,initial.unique,initial.nodeTags⟩

/-- The exact production GC postorder walks and final range normalization
preserve Pool, Accounting, unique tag keys and live-node/tag-index coherence.
Error outputs retain these data invariants; they are not counted as successful
or UB-free executions. Full valid-Rust borrowing histories remain separate. -/
theorem preserves (tree : BorrowTree) (liveTags : Array BorTag) (initial : Invariant tree) :
    Invariant (tree.removeUnreachableTags liveTags).tree := by
  apply GeneralBorrowGcRootInvariant.preserves Invariant tree liveTags initial
  · intro current root good
    exact GeneralBorrowGcWhileInvariant.preserves Invariant remove_step
      (fun current index oldNode newNode present tag good => update_step current index oldNode newNode present tag good)
      current root liveTags good
  · intro current good
    exact ⟨good.pool,good.accounting,good.unique,good.nodeTags⟩

/-- Allocation creation followed by the actual full GC operation requires no
external allocator-history invariant. This theorem concerns data preservation. -/
theorem new_gc (rootTag : BorTag) (size : Miri.ABI.Size) (liveTags : Array BorTag) :
    Invariant ((BorrowTree.new rootTag size).removeUnreachableTags liveTags).tree :=
  preserves _ liveTags (initial rootTag size)
end DuplicatePrefix.GeneralBorrowGcAllocatorFull
