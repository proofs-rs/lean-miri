import duplicate_prefix.GeneralBorrowRecursiveSharedHistory

namespace DuplicatePrefix.GeneralBorrowSharedBankState
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRecursiveSharedResources DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshReleaseMixed DuplicatePrefix.GeneralBorrowOwnership

set_option autoImplicit false in
/-- Previously generated handles are data, with readable range ownership;
selecting one does not execute or assume a successful interpreter operation. -/
structure State (root : UniIndex) (offset len : UInt64) where
  tree : BorrowTree
  resources : Resources tree root
  handles : List UniIndex
  present : ∀ index ∈ handles, ∃ node, tree.nodeAt index = some node
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  owned : ∀ index ∈ handles,
    OwnedOn (GeneralBorrowRange.LocationOwned tree {} index .Read) offset (offset+len) tree.locations

theorem combined (tree : BorrowTree) (index : UniIndex) (location : LocationTree)
    (owned : GeneralBorrowRange.LocationOwned tree {} index .Read location) :
    Combined tree {} index (fun _ => false) location := by
  refine ⟨owned,?_⟩
  intro position valid
  obtain ⟨state,present,permission⟩ := owned.2.permissions position (by rw [←owned.2.locationsAligned];exact valid)
  exact ⟨state,present,by simpa [GeneralBorrowPermissions.Required] using permission⟩

noncomputable def select {root : UniIndex} {offset len : UInt64}
    (s : State root offset len) (index : UniIndex) (member : index ∈ s.handles) :
    GeneralBorrowRecursiveSharedHistory.State root offset len := {
  tree := s.tree, resources := s.resources, parent := index
  node := Classical.choose (s.present index member)
  present := Classical.choose_spec (s.present index member)
  protections := {}, writable := fun _ => false, bounds := s.bounds
  owned := by
    intro position valid positive before after
    exact combined s.tree index _ (s.owned index member position valid positive before after) }
end DuplicatePrefix.GeneralBorrowSharedBankState
