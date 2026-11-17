import duplicate_prefix.GeneralBorrowFreshSharedPrefix
namespace DuplicatePrefix.GeneralBorrowFreshSharedPaths
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

set_option autoImplicit false in
/-- The metadata consequences shared by the two actual leaf-insertion cases.
They cover full production ancestor paths, including traversal fuel changes. -/
structure Attach (before after : TraversalTree) (parent child : Nat) : Prop where
  parentValid : parent < before.nodes.size
  parentDifferent : parent ≠ child
  oldValid : ∀ position, position < before.nodes.size → position ≠ child → position < after.nodes.size
  childPath : after.ancestorPath child = child :: before.ancestorPath parent
  oldPath : ∀ position, position < before.nodes.size → position ≠ child → after.ancestorPath position = before.ancestorPath position
  outsideOld : ∀ position, position < before.nodes.size → position ≠ child → child ∉ after.ancestorPath position

theorem of_append (before after : TraversalTree) (parent : Nat)
    (extension : DuplicatePrefix.GeneralBorrowFreshTopology.Extension before after parent)
    (forest : DuplicatePrefix.GeneralBorrowForest.Forest before) : Attach before after parent before.nodes.size where
  parentValid := extension.parentValid
  parentDifferent := by have := extension.parentValid;omega
  oldValid := by intro position valid different;rw [extension.length];omega
  childPath := DuplicatePrefix.GeneralBorrowFreshTopology.ancestors_new before after parent extension forest
  oldPath := by intro position valid different;exact DuplicatePrefix.GeneralBorrowFreshWriteRestore.append_path before after parent position extension forest valid
  outsideOld := by
    intro position valid different
    rw [DuplicatePrefix.GeneralBorrowFreshWriteRestore.append_path before after parent position extension forest valid]
    intro member
    have bound := (ancestors_data before forest.rank forest.parents before.nodes.size position valid).2 before.nodes.size member
    omega

private theorem vacant_outside (tree : TraversalTree) (forest : DuplicatePrefix.GeneralBorrowForest.Forest tree)
    (index position : Nat) (valid : index < tree.nodes.size) (vacant : tree.nodes[index] = ⟨none,[]⟩)
    (bound : position < tree.nodes.size) (different : position ≠ index) : index ∉ tree.ancestorPath position := by
  have closed : ParentClosed tree (fun node => node < tree.nodes.size ∧ node ≠ index) := by
    intro node known parent edge
    have original : tree.nodes[node].parent = some parent := by
      simpa only [nodeData,Array.getElem?_eq_getElem known.1,Option.getD_some] using edge
    refine ⟨(forest.parents node known.1 parent original).1,?_⟩
    intro same
    subst parent
    exact DuplicatePrefix.GeneralBorrowFreshReuseTopology.no_parent tree forest index valid vacant node known.1 original
  have selected := ancestors_present tree (fun node => node < tree.nodes.size ∧ node ≠ index) closed
    tree.nodes.size position ⟨bound,different⟩
  intro member
  exact (selected index member).2 rfl

theorem of_reuse (before after : TraversalTree) (index parent : Nat)
    (extension : DuplicatePrefix.GeneralBorrowFreshReuseTopology.Extension before after index parent)
    (forest : DuplicatePrefix.GeneralBorrowForest.Forest before) : Attach before after parent index where
  parentValid := extension.parentValid
  parentDifferent := extension.different
  oldValid := by intro position valid different;rw [extension.length];exact valid
  childPath := DuplicatePrefix.GeneralBorrowFreshReuseTopology.ancestors_new before after index parent extension forest
  oldPath := by
    intro position valid different
    unfold TraversalTree.ancestorPath
    rw [extension.length]
    exact DuplicatePrefix.GeneralBorrowFreshReuseTopology.ancestors_old before after index parent extension forest before.nodes.size position valid different
  outsideOld := by
    intro position valid different
    have path : after.ancestorPath position = before.ancestorPath position := by
      unfold TraversalTree.ancestorPath
      rw [extension.length]
      exact DuplicatePrefix.GeneralBorrowFreshReuseTopology.ancestors_old before after index parent extension forest before.nodes.size position valid different
    rw [path]
    exact vacant_outside before forest index position extension.valid extension.vacant valid different

theorem ancestor_self (tree : TraversalTree) (index : Nat) : index ∈ tree.ancestorPath index :=
  List.mem_of_head? (sourceAncestorHead tree tree.nodes.size index)

/-- Two actual leaf-insertion metadata certificates produce the complete
shared-expr/shared-FnEntry prefix and exclude both read-only nodes from the
old mutable anchor's path. No release outcome or ownership restoration is used. -/
theorem two_step (before middle after : TraversalTree) (target expr child : Nat)
    (first : Attach before middle target expr) (second : Attach middle after expr child) :
    after.ancestorPath child = child :: expr :: after.ancestorPath target ∧
      expr ∉ after.ancestorPath target ∧ child ∉ after.ancestorPath target := by
  have targetValid := first.oldValid target first.parentValid first.parentDifferent
  have targetInExpr : target ∈ middle.ancestorPath expr := by
    rw [first.childPath]
    exact List.mem_cons_of_mem expr (ancestor_self before target)
  have childOutsideParent : child ∉ middle.ancestorPath expr := by
    rw [←second.oldPath expr second.parentValid second.parentDifferent]
    exact second.outsideOld expr second.parentValid second.parentDifferent
  have targetDifferent : target ≠ child := by intro same;subst target;exact childOutsideParent targetInExpr
  have paths : after.ancestorPath target = before.ancestorPath target :=
    (second.oldPath target targetValid targetDifferent).trans (first.oldPath target first.parentValid first.parentDifferent)
  refine ⟨?_,?_,second.outsideOld target targetValid targetDifferent⟩
  · rw [second.childPath,first.childPath,paths]
  · rw [second.oldPath target targetValid targetDifferent]
    exact first.outsideOld target first.parentValid first.parentDifferent
end DuplicatePrefix.GeneralBorrowFreshSharedPaths
#print axioms DuplicatePrefix.GeneralBorrowFreshSharedPaths.two_step

open Lean Elab Command in
run_cmd do
  for (name, _) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowFreshSharedPaths.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "{name} depends on unapproved axiom {dependency}"
