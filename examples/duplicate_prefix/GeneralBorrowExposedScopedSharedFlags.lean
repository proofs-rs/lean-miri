import duplicate_prefix.GeneralBorrowFreshSharedSlotFlags
namespace DuplicatePrefix.GeneralBorrowExposedScopedSharedFlags
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildShared
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Hidden (support : Nat → Prop) (tree : BorrowTree) : Prop :=
  ∀ index node, support index.toNat → tree.nodeAt index = some node → node.isExposed = false

/-- Exposure-shape transport is component scoped, including sparse nodes. -/
theorem transfer (support : Nat → Prop) (before after : BorrowTree)
    (same : GeneralBorrowFreshMetadataChildSifa.exposureShape after = GeneralBorrowFreshMetadataChildSifa.exposureShape before)
    (initial : Hidden support before) : Hidden support after := by
  intro query node included present
  have flags := GeneralBorrowFreshMetadataChildSifa.lookup_exposure before after same query
  rw [show after.nodes.get query = some node from present] at flags
  cases old : before.nodeAt query with
  | none => rw [show before.nodes.get query = none from old] at flags;contradiction
  | some previous =>
    have oldFlag := initial query previous included old
    simpa only [show before.nodes.get query = some previous from old,Option.map_some,Option.some.injEq,oldFlag] using flags

/-- Actual shared append preserves hiddenness precisely in the extended
selected component. Old exposed components remain unrestricted. -/
theorem append (input : Input) (support : Nat → Prop) (parent : support input.parent.toNat)
    (initial : Hidden support input.tree) :
    Hidden (fun position => support position ∨ position = (index input).toNat) (result input) := by
  apply transfer _ (stage input) _ (exposure input)
  intro query node included present
  have staged : (GeneralBorrowFreshGraph.attached input.tree (index input) input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent)).nodeAt query = some node := present
  by_cases sameParent : query = input.parent
  · subst query
    have lookup := GeneralBorrowFreshGraph.parent_lookup input.tree (index input) input.parent input.parentNode
      (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) (at_end input) input.parentPresent
    rw [lookup] at staged
    cases staged
    exact initial input.parent input.parentNode parent input.parentPresent
  · by_cases sameNew : query = index input
    · subst query
      have lookup := GeneralBorrowFreshGraph.new_lookup input.tree (index input) input.parent input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) (at_end input) input.parentPresent
      rw [lookup] at staged
      cases staged
      rfl
    · have differentNat : query.toNat ≠ (index input).toNat := by
        intro same
        exact sameNew (GeneralBorrowNodeUpdate.index_injective query (index input) same)
      have lookup := GeneralBorrowFreshGraph.other_lookup input.tree (index input) input.parent query input.parentNode
        (GeneralBorrowFreshAnchor.sharedNode input.newTag input.parent) (at_end input) input.parentPresent sameParent sameNew
      rw [lookup] at staged
      exact initial query node (included.resolve_right differentNat) staged
end DuplicatePrefix.GeneralBorrowExposedScopedSharedFlags
