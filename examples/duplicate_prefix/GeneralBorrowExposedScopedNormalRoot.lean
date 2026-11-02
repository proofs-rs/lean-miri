import duplicate_prefix.GeneralBorrowExposedScopedNormalCache
namespace DuplicatePrefix.GeneralBorrowExposedScopedNormalRoot
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowForest DuplicatePrefix.GeneralBorrowPresence DuplicatePrefix.GeneralBorrowExposedScopedNormal
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- A real parentless forest root and an actual descendant anchor form the
bi-closed scoped component. Closure is derived from reciprocal graph metadata,
not supplied as a visitor-exclusion or successful-access assumption. -/
def component (tree : TraversalTree) (forest : Forest tree) (root anchor : Nat)
    (valid : root < tree.nodes.size) (parentless : tree.nodes[root].parent = none)
    (path : Desc tree root anchor) : Component tree anchor where
  support := Desc tree root
  anchor := path
  parents := by
    intro current member parent edge
    have present := member.valid.2
    change (tree.nodes[current]?.getD ⟨none,[]⟩).parent = some parent at edge
    rw [Array.getElem?_eq_getElem present,Option.getD_some] at edge
    rcases member.parent present edge with same | previous
    · subst current
      rw [parentless] at edge
      cases edge
    · exact previous
  children := by
    intro current member child listed
    have present := member.valid.2
    change child ∈ (tree.nodes[current]?.getD ⟨none,[]⟩).children at listed
    rw [Array.getElem?_eq_getElem present,Option.getD_some] at listed
    obtain ⟨bounded,edge⟩ := forest.childParent current present child listed
    exact Desc.step member bounded edge

/-- Root-component specialization of the pure actual normal access theorem.
Raw compatibility concerns exactly descendants of the selected physical root;
all other components may contain active protected or exposed borrows. -/
theorem normal (tree : NormalTreeState) (root anchor : Nat) (kind : AccessKind) (mode : ChildrenVisitMode)
    (forest : Forest tree.topology) (rootValid : root < tree.topology.nodes.size)
    (parentless : tree.topology.nodes[root].parent = none) (path : Desc tree.topology root anchor)
    (aligned : tree.locationStates.size = tree.topology.nodes.size)
    (owned : ∀ index, Desc tree.topology root index → index < tree.topology.nodes.size →
      ∃ state, tree.stateAt index = some state ∧ GeneralBorrowPermissions.AccessOwned state kind
        (GeneralBorrowAnchor.relation tree anchor index) (tree.protectedNodes.contains index)) :
    (tree.performAccess anchor kind mode).status = .Completed :=
  GeneralBorrowExposedScopedNormal.normal tree anchor kind mode forest path.valid.2 aligned
    (component tree.topology forest root anchor rootValid parentless path) owned
end DuplicatePrefix.GeneralBorrowExposedScopedNormalRoot
