import duplicate_prefix.GeneralBorrowSharedNormalRelations
namespace DuplicatePrefix.GeneralBorrowFreshNormalComponent
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowPresence GeneralBorrowExposedScopedNormal
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw topology patch common to actual append and vacant-slot reuse. -/
structure Patch (before after : TraversalTree) (parent child : Nat) : Prop where
  leaf : nodeData after child = ⟨some parent,[]⟩
  oldParents : ∀ index, index ≠ child → (nodeData after index).parent = (nodeData before index).parent
  oldChildren : ∀ index, index ≠ child → ∀ query ∈ (nodeData after index).children,
    query = child ∨ query ∈ (nodeData before index).children

def extended (support : Nat → Prop) (child : Nat) : Nat → Prop := fun index => index = child ∨ support index

/-- Exact graph closure for the new shared source or the original source.
The same extended component works for both; permission kinds remain separate. -/
def component (before after : TraversalTree) (parent child : Nat)
    (old : Component before parent) (patch : Patch before after parent child)
    (anchor : Nat) (selected : anchor = parent ∨ anchor = child) : Component after anchor where
  support := extended old.support child
  anchor := by
    rcases selected with original | fresh
    · subst anchor;exact .inr old.anchor
    · subst anchor;exact .inl rfl
  parents := by
    intro current included parentNode edge
    by_cases fresh : current = child
    · subst current
      rw [patch.leaf] at edge
      have same : parent = parentNode := Option.some.inj edge
      rw [←same]
      exact .inr old.anchor
    · have oldIncluded : old.support current := included.resolve_left fresh
      exact .inr (old.parents current oldIncluded parentNode ((patch.oldParents current fresh).symm.trans edge))
  children := by
    intro current included query member
    by_cases fresh : current = child
    · subst current
      rw [patch.leaf] at member
      cases member
    · rcases patch.oldChildren current fresh query member with newChild | oldChild
      · exact .inl newChild
      · exact .inr (old.children current (included.resolve_left fresh) query oldChild)

/-- The actual append-extension graph supplies Patch on all Nat indices,
including out-of-bounds defaults; no traversal or ownership is assumed. -/
theorem of_append (before after : TraversalTree) (parent : Nat)
    (extension : GeneralBorrowFreshTopology.Extension before after parent) : Patch before after parent before.nodes.size := by
  have freshValid : before.nodes.size < after.nodes.size := by rw [extension.length];omega
  refine ⟨?_,?_,?_⟩
  · simp only [nodeData,Array.getElem?_eq_getElem freshValid,Option.getD_some,extension.leaf]
  · intro index different
    by_cases valid : index < before.nodes.size
    · have validAfter : index < after.nodes.size := by rw [extension.length];omega
      simpa only [nodeData,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem validAfter,Option.getD_some] using extension.parents index valid
    · have invalidAfter : after.nodes.size ≤ index := by rw [extension.length];omega
      simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Array.getElem?_eq_none invalidAfter,Option.getD_none]
  · intro index different query member
    by_cases valid : index < before.nodes.size
    · have validAfter : index < after.nodes.size := by rw [extension.length];omega
      simp only [nodeData,Array.getElem?_eq_getElem validAfter,Option.getD_some,extension.children index valid,List.mem_append] at member
      rcases member with previous | fresh
      · exact .inr (by simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using previous)
      · split at fresh
        · exact .inl (by simpa using fresh)
        · cases fresh
    · have invalidAfter : after.nodes.size ≤ index := by rw [extension.length];omega
      simp only [nodeData,Array.getElem?_eq_none invalidAfter,Option.getD_none] at member
      cases member

theorem of_reuse (before after : TraversalTree) (child parent : Nat)
    (extension : GeneralBorrowFreshReuseTopology.Extension before after child parent) : Patch before after parent child := by
  have freshValid : child < after.nodes.size := by rw [extension.length];exact extension.valid
  refine ⟨?_,?_,?_⟩
  · simp only [nodeData,Array.getElem?_eq_getElem freshValid,Option.getD_some,extension.leaf]
  · intro index different
    by_cases valid : index < before.nodes.size
    · have validAfter : index < after.nodes.size := by rw [extension.length];exact valid
      simpa only [nodeData,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem validAfter,Option.getD_some] using extension.parents index valid different
    · have invalidAfter : after.nodes.size ≤ index := by rw [extension.length];omega
      simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Array.getElem?_eq_none invalidAfter,Option.getD_none]
  · intro index different query member
    by_cases valid : index < before.nodes.size
    · have validAfter : index < after.nodes.size := by rw [extension.length];exact valid
      simp only [nodeData,Array.getElem?_eq_getElem validAfter,Option.getD_some,extension.children index valid different,List.mem_append] at member
      rcases member with previous | fresh
      · exact .inr (by simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using previous)
      · split at fresh
        · exact .inl (by simpa using fresh)
        · cases fresh
    · have invalidAfter : after.nodes.size ≤ index := by rw [extension.length];omega
      simp only [nodeData,Array.getElem?_eq_none invalidAfter,Option.getD_none] at member
      cases member

end DuplicatePrefix.GeneralBorrowFreshNormalComponent
