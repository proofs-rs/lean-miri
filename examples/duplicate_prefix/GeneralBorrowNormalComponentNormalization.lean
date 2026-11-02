import duplicate_prefix.DuplicatePrefixBorrowAuthorization
import duplicate_prefix.GeneralBorrowExposedScopedNormalRoot

namespace DuplicatePrefix.GeneralBorrowNormalComponentNormalization
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowForest GeneralBorrowPresence
set_option autoImplicit false

/-- Closure already supplied by a normal certificate includes every ancestor
of an included node. This uses graph edges, not visitor completion. -/
theorem contains_ancestor (tree : TraversalTree) (anchor : Nat)
    (component : GeneralBorrowExposedScopedNormal.Component tree anchor)
    (root node : Nat) (path : Desc tree root node)
    (included : component.support node) : component.support root := by
  revert included
  induction path with
  | refl valid => intro included; exact included
  | @step parent child earlier valid edge ih =>
    intro included
    apply ih
    apply component.parents child included parent
    simpa only [nodeData, Array.getElem?_eq_getElem valid, Option.getD_some] using edge

/-- The same certificate includes all descendants of each included root. -/
theorem contains_descendant (tree : TraversalTree) (forest : Forest tree) (anchor : Nat)
    (component : GeneralBorrowExposedScopedNormal.Component tree anchor)
    (root node : Nat) (path : Desc tree root node)
    (included : component.support root) : component.support node := by
  induction path with
  | refl => exact included
  | @step parent child earlier valid edge ih =>
    obtain ⟨parentValid, member⟩ := forest.parentChild child valid parent edge
    apply component.children parent ih child
    simpa only [nodeData, Array.getElem?_eq_getElem parentValid, Option.getD_some] using member

/-- An arbitrary larger normal component can be restricted to the actual
physical root's descendants. No new permission condition is required. The
component identity in the conclusion is explicit for later root separation. -/
theorem canonical (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor : UniIndex) (root : Nat)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (rootValid : root < (source_normal_projection tree location protections).topology.nodes.size)
    (parentless : (source_normal_projection tree location protections).topology.nodes[root].parent = none)
    (path : Desc (source_normal_projection tree location protections).topology root anchor.toNat)
    (authorization : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor) :
    ∃ next : DuplicatePrefixBorrowAuthorization.Normal tree location protections anchor,
      next.component.support = Desc (source_normal_projection tree location protections).topology root := by
  have rootIncluded := contains_ancestor _ anchor.toNat authorization.component root anchor.toNat path authorization.component.anchor
  let chosen := GeneralBorrowExposedScopedNormalRoot.component
    (source_normal_projection tree location protections).topology forest root anchor.toNat rootValid parentless path
  refine ⟨{component := chosen, permissions := ?_}, rfl⟩
  intro kind index supported valid
  exact authorization.permissions kind index
    (contains_descendant _ forest anchor.toNat authorization.component root index supported rootIncluded) valid

/-- Two different parentless roots have disjoint descendant components. -/
theorem roots_disjoint (tree : TraversalTree) (left right node : Nat)
    (leftValid : left < tree.nodes.size) (rightValid : right < tree.nodes.size)
    (leftParentless : tree.nodes[left].parent = none)
    (rightParentless : tree.nodes[right].parent = none) (different : left ≠ right)
    (fromLeft : Desc tree left node) (fromRight : Desc tree right node) : False := by
  have parentless_ancestor : ∀ root current, ∀ path : Desc tree root current,
      (tree.nodes[current]'path.valid.2).parent = none → root = current := by
    intro root current path parentless
    cases path with
    | refl => rfl
    | step earlier valid edge => rw [parentless] at edge; cases edge
  rcases fromLeft.comparable fromRight with across | across
  · exact different (parentless_ancestor left right across rightParentless)
  · exact different (parentless_ancestor right left across leftParentless).symm

end DuplicatePrefix.GeneralBorrowNormalComponentNormalization
