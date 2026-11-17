import duplicate_prefix.GeneralBorrowExposedScopedNormal
import duplicate_prefix.GeneralBorrowFreshTopology
namespace DuplicatePrefix.GeneralBorrowExposedScopedChildComponent
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowPresence GeneralBorrowTopology
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Fresh concrete child insertion extends the graph component itself, with
no conditions on permissions or exposure in any other component. -/
def append (before after : TraversalTree) (parent : Nat)
    (extension : GeneralBorrowFreshTopology.Extension before after parent)
    (component : GeneralBorrowExposedScopedNormal.Component before parent) :
    GeneralBorrowExposedScopedNormal.Component after before.nodes.size where
  support := fun position => component.support position ∨ position = before.nodes.size
  anchor := Or.inr rfl
  parents := by
    intro position supported earlier edge
    by_cases valid : position < after.nodes.size
    · have source : (after.nodes[position]'valid).parent = some earlier := by
        simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using edge
      by_cases fresh : position = before.nodes.size
      · subst position
        rw [extension.leaf] at source
        have same : parent = earlier := Option.some.inj source
        subst earlier
        exact Or.inl component.anchor
      · have old : position < before.nodes.size := by rw [extension.length] at valid;omega
        have oldEdge : (before.nodes[position]'old).parent = some earlier := (extension.parents position old).symm.trans source
        apply Or.inl
        apply component.parents position (supported.resolve_right fresh) earlier
        simpa only [nodeData,Array.getElem?_eq_getElem old,Option.getD_some] using oldEdge
    · simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Option.getD_none] at edge
      cases edge
  children := by
    intro position supported child member
    by_cases valid : position < after.nodes.size
    · have source : child ∈ (after.nodes[position]'valid).children := by
        simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using member
      by_cases fresh : position = before.nodes.size
      · subst position
        rw [extension.leaf] at source
        cases source
      · have old : position < before.nodes.size := by rw [extension.length] at valid;omega
        rw [extension.children position old] at source
        rcases List.mem_append.mp source with earlier | newChild
        · apply Or.inl
          apply component.children position (supported.resolve_right fresh) child
          simpa only [nodeData,Array.getElem?_eq_getElem old,Option.getD_some] using earlier
        · split at newChild
          · exact Or.inr (by simpa using newChild)
          · cases newChild
    · simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Option.getD_none] at member
      cases member
end DuplicatePrefix.GeneralBorrowExposedScopedChildComponent
