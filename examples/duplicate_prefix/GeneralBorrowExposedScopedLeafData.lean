import duplicate_prefix.GeneralBorrowExposedScopedMixedRebase
namespace DuplicatePrefix.GeneralBorrowExposedScopedLeafData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowExposedKnownRootState
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- A positive self counter is derived from an actual exposed supporting leaf,
so its conditional profile is local even when it is protected Unique. -/
theorem readable (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536)
    (states : ∀ index node, area.support index → tree.nodes.get index = some node →
      node.isExposed = true ∧
      GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections index node) .Read = true ∧
      (GeneralBorrowWildcardVirtualLeaf.effective location index node).possible = true) :
    Readable tree location protections := by
  intro index node included present
  obtain ⟨exposed,support,possible⟩ := states index node included present
  have positive := GeneralBorrowExposureCardinality.exposed_self location.exposedCache tree.nodes
    (GeneralBorrowExposureCardinality.effective location protections) coherent short index node present exposed .Read support
  change 0 < GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index .Read at positive
  have nonzero : zero location index = false := by simp [zero,Nat.ne_of_gt positive]
  rw [GeneralBorrowExposedConditionalReadPermissions.Condition,nonzero]
  refine ⟨possible,?_⟩
  have permissions : (GeneralBorrowWildcardVirtualLeaf.effective location index node).permission ≠ .Disabled := by
    intro disabled
    simp only [GeneralBorrowExposureCardinality.effective,GeneralBorrowWildcardVirtualLeaf.effective] at support
    change GeneralBorrowExposureCardinality.supports
      ((GeneralBorrowWildcardVirtualLeaf.effective location index node).permission.strongestAllowedLocalAccess _) .Read = true at support
    rw [disabled] at support
    cases held : protections.contains node.tag <;> simp [held,Permission.strongestAllowedLocalAccess,GeneralBorrowExposureCardinality.supports,GeneralBorrowExposureAncestorFold.supportsRead] at support
  exact permissions

/-- A leaf's supporting component record has a singleton graph support. Covers
is reflexive, independent of the shape or exposure in all other roots. -/
def virtual (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[]) (included : area.support root)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (profile : Readable tree location protections) : Data tree location root protections where
  support := fun index => index = root
  rooted := rfl
  present := by intro index same;subst index;exact ⟨node,present⟩
  children := by
    intro index queried same found child member
    subst index
    have sameNode := Option.some.inj (present.symm.trans found)
    subst queried
    rw [leaf] at member
    cases member
  covers := by intro index same;subst index;intro row member ancestor;exact ancestor
  coherent := coherent
  short := short
  depth := depth
  included := by intro index same;subst index;exact included
  readable := profile

/-- A real exposed supporting first leaf provides its own finite witness. -/
def primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root = some node) (leaf : node.children = #[]) (included : area.support root)
    (exposed : node.isExposed = true)
    (support : GeneralBorrowExposureCardinality.supports (GeneralBorrowExposureCardinality.effective location protections root node) .Read = true)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (short : tree.nodes.size < 65536) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (profile : Readable tree location protections) (graph : GeneralBorrowExposedNonleafPrimaryPath.Reciprocal tree) :
    GeneralBorrowExposedKnownRootPrimaryWitness.Data tree location root protections where
  base := virtual tree location protections root node present leaf included coherent short depth profile
  graph := graph
  witness := root
  node := node
  present := present
  exposed := exposed
  support := support
  path := .refl root node present
end DuplicatePrefix.GeneralBorrowExposedScopedLeafData
