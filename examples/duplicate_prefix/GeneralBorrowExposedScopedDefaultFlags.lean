import duplicate_prefix.GeneralBorrowFreshMetadataChildDefault
import duplicate_prefix.GeneralBorrowExposedScopedSharedFlags
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultFlags
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open GeneralBorrowExposedScopedSharedFlags (Hidden transfer)

/-- Actual Default append preserves hiddenness precisely in the extended
selected component. Old exposed components remain unrestricted. -/
theorem append (input : Input) (support : Nat → Prop) (parent : support input.parent.toNat)
    (initial : Hidden support input.tree) :
    Hidden (fun position => support position ∨ position = (index input).toNat) (result input) := by
  apply transfer _ (stage input) _ (exposure input)
  intro query node included present
  have staged : (GeneralBorrowFreshGraph.attached input.tree (index input) input.parent input.parentNode
      (GeneralBorrowFreshDefaultChild.child input.newTag input.parent)).nodeAt query = some node := present
  by_cases sameParent : query = input.parent
  · subst query
    have lookup := GeneralBorrowFreshGraph.parent_lookup input.tree (index input) input.parent input.parentNode
      (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) (at_end input) input.parentPresent
    rw [lookup] at staged
    cases staged
    exact initial input.parent input.parentNode parent input.parentPresent
  · by_cases sameNew : query = index input
    · subst query
      have lookup := GeneralBorrowFreshGraph.new_lookup input.tree (index input) input.parent input.parentNode
        (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) (at_end input) input.parentPresent
      rw [lookup] at staged
      cases staged
      rfl
    · have differentNat : query.toNat ≠ (index input).toNat := by
        intro same
        exact sameNew (GeneralBorrowNodeUpdate.index_injective query (index input) same)
      have lookup := GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent query input.parentNode
        (GeneralBorrowFreshDefaultChild.child input.newTag input.parent) (at_end input) input.parentPresent sameParent sameNew
      rw [lookup] at staged
      exact initial query node (included.resolve_right differentNat) staged
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultFlags
