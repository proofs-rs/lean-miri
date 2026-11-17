import duplicate_prefix.GeneralBorrowFreshReuseTopology
import duplicate_prefix.DuplicatePrefixBorrowAuthorization
namespace DuplicatePrefix.GeneralBorrowDirectParentGeometry
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowTopology GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem terminal_step (tree : TraversalTree) (fuel current : Nat)
    (terminal : (nodeData tree (sourceAncestorPath tree fuel current).getLast!).parent = none) :
    sourceAncestorPath tree (fuel+1) current = sourceAncestorPath tree fuel current := by
  induction fuel generalizing current with
  | zero =>
    have edge : (nodeData tree current).parent = none := by simpa [ancestor_zero] using terminal
    rw [ancestor_succ,edge,ancestor_zero]
  | succ fuel ih =>
    rw [ancestor_succ] at terminal
    rw [ancestor_succ,ancestor_succ]
    cases edge : (nodeData tree current).parent with
    | none => simp only [edge]
    | some earlier =>
      simp only [edge] at terminal ⊢
      have lastEq : (current :: sourceAncestorPath tree fuel earlier).getLast! =
          (sourceAncestorPath tree fuel earlier).getLast! := by
        simp only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil
          (GeneralBorrowTerminal.ancestors_nonempty tree fuel earlier)]
      rw [lastEq] at terminal
      rw [ih earlier terminal]

/-- A direct parent's complete path needs one less than the table-size fuel,
since its strictly lower-ranked path cannot contain its child. -/
theorem parent_short (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (child parent : Nat) (valid : child < tree.nodes.size)
    (edge : tree.nodes[child].parent = some parent) :
    sourceAncestorPath tree (tree.nodes.size-1) parent = tree.ancestorPath parent := by
  have relation := forest.parents child valid parent edge
  have data := ancestors_data tree forest.rank forest.parents (tree.nodes.size-1) parent relation.1
  have subset : sourceAncestorPath tree (tree.nodes.size-1) parent ⊆ (List.range tree.nodes.size).erase child := by
    intro position member
    have known := data.2 position member
    have different : position ≠ child := by intro equal;subst position;omega
    exact (List.mem_erase_of_ne different).mpr (List.mem_range.mpr known.1)
  have bound := data.1.length_le_of_subset subset
  rw [List.length_erase_of_mem (List.mem_range.mpr valid),List.length_range] at bound
  have terminal : (nodeData tree (sourceAncestorPath tree (tree.nodes.size-1) parent).getLast!).parent = none := by
    rcases GeneralBorrowTerminal.terminal_or_full tree forest (tree.nodes.size-1) parent relation.1 with terminal | full
    · exact terminal
    · omega
  have stable := terminal_step tree (tree.nodes.size-1) parent terminal
  have fuelEq : tree.nodes.size-1+1 = tree.nodes.size := by omega
  simpa only [fuelEq,TraversalTree.ancestorPath] using stable.symm

/-- Direct-parent paths hold for arbitrary descendant and sibling subtrees. -/
theorem paths (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (child parent : Nat) (valid : child < tree.nodes.size)
    (edge : tree.nodes[child].parent = some parent) :
    tree.ancestorPath child = child :: tree.ancestorPath parent ∧ child ∉ tree.ancestorPath parent := by
  have relation := forest.parents child valid parent edge
  constructor
  · change sourceAncestorPath tree tree.nodes.size child = _
    have size : tree.nodes.size = (tree.nodes.size-1)+1 := by omega
    rw [size,ancestor_succ]
    have lookup : (nodeData tree child).parent = some parent := by
      simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using edge
    rw [lookup]
    simp only
    rw [parent_short tree forest child parent valid edge]
  · intro member
    have known := (ancestors_data tree forest.rank forest.parents tree.nodes.size parent relation.1).2 child member
    omega
end DuplicatePrefix.GeneralBorrowDirectParentGeometry
