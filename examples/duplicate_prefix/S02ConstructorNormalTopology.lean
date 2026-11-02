import duplicate_prefix.GeneralBorrowFreshNormalComponent
import duplicate_prefix.DuplicatePrefixScalarAuthorization

namespace DuplicatePrefix.S02ConstructorNormalTopology
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowPresence GeneralBorrowExposedScopedNormal GeneralBorrowFreshNormalComponent
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 200000

/-- A reused vacant slot need not have been excluded from an arbitrary old
normal component's support. Remove it before conditionally adding the child. -/
def Rebased (support : Nat → Prop) (parent child query : Nat) : Prop :=
  (support query ∧ query ≠ child) ∨ (query = child ∧ support parent)

/-- Fresh-leaf attachment preserves a normal component anchored at any old
live source, including a source in another component. The edge premises are
pure physical graph facts: the vacant slot had no incident edges, and every
new incoming edge to the child is from its constructor parent. -/
def component (before after : TraversalTree) (parent child anchor : Nat)
    (old : Component before anchor) (anchorDifferent : anchor ≠ child) (parentDifferent : parent ≠ child)
    (patch : Patch before after parent child)
    (noParent : ∀ current,(nodeData before current).parent ≠ some child)
    (childEdge : ∀ current,current ≠ child → child ∈ (nodeData after current).children → current = parent) :
    Component after anchor where
  support := Rebased old.support parent child
  anchor := .inl ⟨old.anchor,anchorDifferent⟩
  parents := by
    intro current included earlier edge
    rcases included with ⟨oldIncluded,different⟩ | ⟨fresh,parentIncluded⟩
    · have previous : (nodeData before current).parent = some earlier :=
        (patch.oldParents current different).symm.trans edge
      have earlierDifferent : earlier ≠ child := by
        intro same
        rw [same] at previous
        exact noParent current previous
      exact .inl ⟨old.parents current oldIncluded earlier previous,earlierDifferent⟩
    · subst current
      rw [patch.leaf] at edge
      have same : parent = earlier := Option.some.inj edge
      subst earlier
      exact .inl ⟨parentIncluded,parentDifferent⟩
  children := by
    intro current included query member
    rcases included with ⟨oldIncluded,different⟩ | ⟨fresh,_⟩
    · by_cases fresh : query = child
      · subst query
        exact .inr ⟨rfl,by rw [←childEdge current different member];exact oldIncluded⟩
      · rcases patch.oldChildren current different query member with isFresh | previous
        · exact False.elim (fresh isFresh)
        · exact .inl ⟨old.children current oldIncluded query previous,fresh⟩
    · subst current
      rw [patch.leaf] at member
      cases member

/-- An isolated dummy slot in a reciprocal forest has no incoming parent edge,
including from any out-of-bounds default node. -/
theorem no_parent (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (child : Nat) (isolated : nodeData tree child = ⟨none,[]⟩) :
    ∀ current,(nodeData tree current).parent ≠ some child := by
  intro current edge
  by_cases valid : current < tree.nodes.size
  · have physical : tree.nodes[current].parent = some child := by
      simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using edge
    obtain ⟨childValid,member⟩ := forest.parentChild current valid child physical
    have empty : tree.nodes[child].children = [] := by
      have shape : tree.nodes[child] = ⟨none,[]⟩ := by
        simpa only [nodeData,Array.getElem?_eq_getElem childValid,Option.getD_some] using isolated
      rw [shape]
    rw [empty] at member
    cases member
  · simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Option.getD_none] at edge
    cases edge

/-- Reciprocity identifies every incoming child edge with the new leaf's
actual parent. -/
theorem child_edge (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (parent child : Nat) (leaf : nodeData tree child = ⟨some parent,[]⟩) :
    ∀ current,current ≠ child → child ∈ (nodeData tree current).children → current = parent := by
  intro current _ member
  by_cases valid : current < tree.nodes.size
  · have physical : child ∈ tree.nodes[current].children := by
      simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using member
    obtain ⟨childValid,edge⟩ := forest.childParent current valid child physical
    have shape : tree.nodes[child] = ⟨some parent,[]⟩ := by
      simpa only [nodeData,Array.getElem?_eq_getElem childValid,Option.getD_some] using leaf
    rw [shape] at edge
    exact (Option.some.inj edge).symm
  · simp only [nodeData,Array.getElem?_eq_none (Nat.le_of_not_gt valid),Option.getD_none] at member
    cases member

/-- Reusable normal-component transport uses only the two physical forest
certificates, the vacant slot shape and the real constructor topology patch. -/
def of_forests (before after : TraversalTree) (parent child anchor : Nat)
    (old : Component before anchor) (anchorDifferent : anchor ≠ child) (parentDifferent : parent ≠ child)
    (oldForest : GeneralBorrowForest.Forest before) (newForest : GeneralBorrowForest.Forest after)
    (isolated : nodeData before child = ⟨none,[]⟩) (patch : Patch before after parent child) :
    Component after anchor :=
  component before after parent child anchor old anchorDifferent parentDifferent patch
    (no_parent before oldForest child isolated) (child_edge after newForest parent child patch.leaf)

/-- Append geometry constructs the arbitrary-anchor normal component directly. -/
def of_append (before after : TraversalTree) (parent anchor : Nat)
    (extension : GeneralBorrowFreshTopology.Extension before after parent)
    (forest : GeneralBorrowForest.Forest before) (old : Component before anchor)
    (anchorValid : anchor < before.nodes.size) : Component after anchor :=
  of_forests before after parent before.nodes.size anchor old (by omega)
    (by have := extension.parentValid;omega) forest
    (GeneralBorrowFreshTopology.extended_forest before after parent extension forest)
    (by simp only [nodeData,Array.getElem?_eq_none (Nat.le_refl _),Option.getD_none])
    (GeneralBorrowFreshNormalComponent.of_append before after parent extension)

/-- Bounded vacant-slot reuse also supports any old live anchor, without
requiring its old support to exclude the reused slot. -/
def of_reuse (before after : TraversalTree) (parent child anchor : Nat)
    (extension : GeneralBorrowFreshReuseTopology.Extension before after child parent)
    (forest : GeneralBorrowForest.Forest before) (old : Component before anchor)
    (anchorDifferent : anchor ≠ child) : Component after anchor :=
  of_forests before after parent child anchor old anchorDifferent extension.different forest
    (GeneralBorrowFreshReuseTopology.extended_forest before after child parent extension forest)
    (by simp only [nodeData,Array.getElem?_eq_getElem extension.valid,Option.getD_some,extension.vacant])
    (GeneralBorrowFreshNormalComponent.of_reuse before after child parent extension)

/-- The actual lazy mutable child's scalar state is compatible with every
normal Read/Write relation and protector bit. SIFA values do not affect scalar
compatibility, so this remains available after ancestor SIFA transport. -/
theorem lazy_compatible (kind : AccessKind) (related : AccessRelatedness)
    (held : Bool) (sifa : IdempotentForeignAccess) :
    DuplicatePrefixScalarAuthorization.Compatible ⟨.ReservedFrz false,false,sifa⟩ kind related held := by
  cases kind <;> cases related <;> cases held <;>
    simp [DuplicatePrefixScalarAuthorization.Compatible,GeneralBorrowProtectedReadCompatible.Compatible,
      GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

end DuplicatePrefix.S02ConstructorNormalTopology

open Lean Elab Command in
run_cmd do
  for name in #[``DuplicatePrefix.S02ConstructorNormalTopology.component,
      ``DuplicatePrefix.S02ConstructorNormalTopology.of_append,
      ``DuplicatePrefix.S02ConstructorNormalTopology.of_reuse,
      ``DuplicatePrefix.S02ConstructorNormalTopology.lazy_compatible] do
    for ax in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
        throwError "unapproved axiom {ax}"
