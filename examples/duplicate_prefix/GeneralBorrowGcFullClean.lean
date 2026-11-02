import duplicate_prefix.GeneralBorrowGcRootInvariant
import duplicate_prefix.GeneralBorrowGcWhileInvariant
namespace DuplicatePrefix.GeneralBorrowGcFullClean
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcVacantClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The production child walker preserves all vacant permission slots, including
partial states returned by malformed-graph errors. -/
theorem children_preserves (tree : BorrowTree) (root : UniIndex) (liveTags : Array BorTag)
    (good : VacantClean tree) : VacantClean (gc_root_children tree root liveTags).tree := by
  apply GeneralBorrowGcWhileInvariant.preserves VacantClean
    (fun current index valid => remove_preserves current index valid)
    (fun current index oldNode newNode _ _ valid => insert_preserves current index newNode valid)
    tree root liveTags good

/-- Full production GC retains the allocation-wide vacant-slot permission
invariant through child removals, node rewrites, normalization and merging.
No GC success, eligibility, graph or post-state cleanliness is assumed. This is
invariant preservation, not a claim that GC errors are successful execution. -/
theorem preserves (tree : BorrowTree) (liveTags : Array BorTag) (good : VacantClean tree) :
    VacantClean (tree.removeUnreachableTags liveTags).tree :=
  GeneralBorrowGcRootInvariant.preserves VacantClean tree liveTags good
    (fun current root valid => children_preserves current root liveTags valid)
    (fun current valid => GeneralBorrowGcRangeClean.finish_preserves current valid)

/-- Actual allocation followed by full GC forms the invariant from constructor
semantics alone, regardless of whether GC returns success or an error. -/
theorem allocation_gc (tag : BorTag) (size : Size) (liveTags : Array BorTag) :
    VacantClean ((BorrowTree.new tag size).removeUnreachableTags liveTags).tree :=
  preserves _ liveTags (initial tag size)
end DuplicatePrefix.GeneralBorrowGcFullClean
