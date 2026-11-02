import duplicate_prefix.GeneralBorrowFreshWriteRestore

namespace DuplicatePrefix.GeneralBorrowFreshReadExtension
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions

/-- An unprotected possible leaf preserves every old Read anchor when old states and ancestor paths are retained. -/
theorem extension_owned (before after : NormalTreeState) (anchor child : Nat)
    (owned : AnchorOwned before anchor .Read)
    (valid : anchor < after.topology.nodes.size)
    (locations : after.locationStates.size = after.topology.nodes.size)
    (defaults : after.defaultStates.size = after.topology.nodes.size)
    (oldPosition : ∀ position, position < after.topology.nodes.size → position ≠ child → position < before.topology.nodes.size)
    (oldState : ∀ position, position < before.topology.nodes.size → position ≠ child → after.stateAt position = before.stateAt position)
    (oldProtection : ∀ position, position < before.topology.nodes.size → position ≠ child → after.protectedNodes.contains position = before.protectedNodes.contains position)
    (path : after.topology.ancestorPath anchor = before.topology.ancestorPath anchor)
    (foreignChild : child ∉ after.topology.ancestorPath anchor)
    (state : LocationState) (present : after.stateAt child = some state)
    (possible : state.possible = true) (released : after.protectedNodes.contains child = false) :
    AnchorOwned after anchor .Read := by
  refine ⟨valid,locations,defaults,?_⟩
  intro position bound
  by_cases same : position = child
  · subst position
    refine ⟨state,present,?_⟩
    simp only [AccessOwned,Owned,relation,foreignChild,↓reduceIte,released]
    exact ⟨possible,Or.inl rfl⟩
  · have oldBound := oldPosition position bound same
    obtain ⟨old,present,permission⟩ := owned.permissions position oldBound
    refine ⟨old,(oldState position oldBound same).trans present,?_⟩
    simpa only [relation,path,oldProtection position oldBound same] using permission

end DuplicatePrefix.GeneralBorrowFreshReadExtension
