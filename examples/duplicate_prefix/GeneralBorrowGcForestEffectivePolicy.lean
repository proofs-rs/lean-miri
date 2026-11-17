import duplicate_prefix.GeneralBorrowGcDefaultWhile
import duplicate_prefix.GeneralBorrowGcEffectivePolicy
import duplicate_prefix.GeneralBorrowGcRootInvariant

namespace DuplicatePrefix.GeneralBorrowGcForestEffectivePolicy
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcEffectivePolicy

/-- The exact arbitrary-depth postorder walker preserves interval-dependent
permission policies. Its actual node updates preserve lazy defaults; tag-only
update stability is neither required nor assumed. Errors preserve data only. -/
theorem children (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree)
    (root : UniIndex) (live : Array BorTag) (good : Policy allowed tree) :
    Policy allowed (source_gc_children tree root live).tree :=
  GeneralBorrowGcDefaultWhile.preserves (Policy allowed) (remove allowed)
    (update allowed) tree root live good

/-- Full production GC preserves effective permission constraints for arbitrary
finite graphs and live-tag sets, through actual walks, trimming and merging.
This theorem does not assert that the GC operation succeeds. -/
theorem preserves (allowed : UniIndex → LocationState → Prop) (tree : BorrowTree)
    (live : Array BorTag) (good : Policy allowed tree) :
    Policy allowed (tree.removeUnreachableTags live).tree := by
  apply GeneralBorrowGcRootInvariant.preserves (Policy allowed) tree live good
  · intro current root initial
    exact children allowed current root live initial
  · intro current initial
    exact merge allowed _ (trim allowed _ initial)
end DuplicatePrefix.GeneralBorrowGcForestEffectivePolicy
