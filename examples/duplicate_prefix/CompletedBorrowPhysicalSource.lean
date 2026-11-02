import duplicate_prefix.CompletedBorrowAncestry

/-! In a single physical component, completed source ancestry agrees with
physical source ancestry. The finite completion cannot leave the component
through a virtual edge and return along its source's physical parent chain. -/
namespace DuplicatePrefix.CompletedBorrowPhysicalSource
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath CandidateStableCallOwnership CompletedBorrowAncestry
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem below_depth_le {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {first last : UniIndex}
    (below : Below completion first last) :
    (completion.depths[first.toNat]?).getD 0 ≤ (completion.depths[last.toNat]?).getD 0 := by
  induction below with
  | refl => exact Nat.le_refl _
  | @step parent child edge prior ih =>
    have strict := (complete.2.2.2.2.2.2 child parent edge).2.2
    exact Nat.le_trans ih (Nat.le_of_lt strict)

theorem same_root_ancestor {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {root query source : UniIndex} {rootNode queryNode : TreeNode}
    (rootPresent : tree.nodes.get root = some rootNode) (parentless : rootNode.parent = none)
    (queryPresent : tree.nodes.get query = some queryNode)
    (rootQuery : Path tree root query) (rootSource : Path tree root source)
    (below : Below completion query source) : Path tree query source := by
  rcases physical_or_attachment complete queryPresent below with physical | attachment
  · exact physical
  · obtain ⟨origin,next,originNode,nextNode,path,_,_,nextPresent,nextParentless,edge,after⟩ := attachment
    have nextRoot : Below completion next root := by
      rcases physical_suffix complete rootSource after with above | physicalNext
      · exact above
      · have same := physical_roots_unique rootPresent parentless nextPresent nextParentless
          physicalNext (.refl _ nextNode nextPresent)
        subst next
        exact .refl root
    have rootOrigin := physical_below complete (path_trans rootQuery path)
    have before := below_depth_le complete rootOrigin
    have strict := (complete.2.2.2.2.2.2 next origin edge).2.2
    have afterRoot := below_depth_le complete nextRoot
    omega

/-- This is the graph conversion needed by a real normal component's
Local/Foreign permission clauses, rather than a successful-normal premise. -/
theorem same_root_ancestor_iff {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {root query source : UniIndex} {rootNode queryNode : TreeNode}
    (rootPresent : tree.nodes.get root = some rootNode) (parentless : rootNode.parent = none)
    (queryPresent : tree.nodes.get query = some queryNode)
    (rootQuery : Path tree root query) (rootSource : Path tree root source) :
    Below completion query source ↔ Path tree query source :=
  ⟨same_root_ancestor complete rootPresent parentless queryPresent rootQuery rootSource,
    physical_below complete⟩

end DuplicatePrefix.CompletedBorrowPhysicalSource

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CompletedBorrowPhysicalSource." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved physical source ancestry dependency {dependency}"
