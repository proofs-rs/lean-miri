import duplicate_prefix.GeneralBorrowFreshSharedPaths
namespace DuplicatePrefix.GeneralBorrowFreshPathExtension
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshSharedPaths DuplicatePrefix.GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

theorem target_different (before after : TraversalTree) (parent child target : Nat)
    (attach : Attach before after parent child)
    (subset : ∀ position ∈ before.ancestorPath target, position ∈ before.ancestorPath parent) : target ≠ child := by
  have outside := attach.outsideOld parent attach.parentValid attach.parentDifferent
  rw [attach.oldPath parent attach.parentValid attach.parentDifferent] at outside
  intro equal
  exact outside (equal ▸ subset target (ancestor_self before target))

theorem target_path (before after : TraversalTree) (parent child target : Nat)
    (attach : Attach before after parent child) (valid : target < before.nodes.size)
    (subset : ∀ position ∈ before.ancestorPath target, position ∈ before.ancestorPath parent) :
    after.ancestorPath target = before.ancestorPath target :=
  attach.oldPath target valid (target_different before after parent child target attach subset)

theorem subset (before after : TraversalTree) (parent child target : Nat)
    (attach : Attach before after parent child) (valid : target < before.nodes.size)
    (included : ∀ position ∈ before.ancestorPath target, position ∈ before.ancestorPath parent) :
    ∀ position ∈ after.ancestorPath target, position ∈ after.ancestorPath child := by
  intro position member
  rw [target_path before after parent child target attach valid included] at member
  rw [attach.childPath]
  exact List.mem_cons_of_mem child (included position member)

theorem escaping (before after : TraversalTree) (parent child target position : Nat)
    (attach : Attach before after parent child) (valid : target < before.nodes.size)
    (included : ∀ item ∈ before.ancestorPath target, item ∈ before.ancestorPath parent)
    (localChild : position ∈ after.ancestorPath child) (foreignTarget : position ∉ after.ancestorPath target) :
    position = child ∨ (position ∈ before.ancestorPath parent ∧ position ∉ before.ancestorPath target) := by
  rw [attach.childPath] at localChild
  rw [target_path before after parent child target attach valid included] at foreignTarget
  rcases List.mem_cons.mp localChild with same | old
  · exact Or.inl same
  · exact Or.inr ⟨old,foreignTarget⟩
end DuplicatePrefix.GeneralBorrowFreshPathExtension
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshPathExtension." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved path extension dependency {dependency}"
