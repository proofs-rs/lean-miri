import duplicate_prefix.GeneralBorrowPresence
namespace DuplicatePrefix.GeneralBorrowTerminal
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowFrontier DuplicatePrefix.GeneralBorrowForest DuplicatePrefix.GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

theorem ancestors_nonempty (tree : TraversalTree) (fuel current : Nat) :
    sourceAncestorPath tree fuel current ≠ [] := by
  intro empty
  have head := sourceAncestorHead tree fuel current
  rw [empty] at head
  cases head

theorem terminal_or_full (tree : TraversalTree) (forest : Forest tree)
    (fuel current : Nat) (valid : current < tree.nodes.size) :
    (nodeData tree (sourceAncestorPath tree fuel current).getLast!).parent = none ∨
      (sourceAncestorPath tree fuel current).length = fuel+1 := by
  induction fuel generalizing current with
  | zero => exact .inr rfl
  | succ fuel ih =>
    rw [ancestor_succ]
    cases parentEq : (nodeData tree current).parent with
    | none => exact .inl (by simpa using parentEq)
    | some parent =>
      have nodeEq : nodeData tree current = tree.nodes[current] := by simp [nodeData,valid]
      have parentValid := (forest.parents current valid parent (by simpa only [nodeEq] using parentEq)).1
      have lastEq : (current :: sourceAncestorPath tree fuel parent).getLast! =
          (sourceAncestorPath tree fuel parent).getLast! := by
        simp only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil (ancestors_nonempty tree fuel parent)]
      rcases ih parent parentValid with terminal | full
      · exact .inl (by simpa only [lastEq] using terminal)
      · exact .inr (by simp only [List.length_cons,full,Nat.add_assoc])

theorem ancestor_terminal (tree : TraversalTree) (forest : Forest tree)
    (current : Nat) (valid : current < tree.nodes.size) :
    (nodeData tree (tree.ancestorPath current).getLast!).parent = none := by
  rcases terminal_or_full tree forest tree.nodes.size current valid with terminal | full
  · exact terminal
  · have data := ancestors_data tree forest.rank forest.parents tree.nodes.size current valid
    have subset : sourceAncestorPath tree tree.nodes.size current ⊆ List.range tree.nodes.size := by
      intro node member
      exact List.mem_range.mpr (data.2 node member).1
    have bound := data.1.length_le_of_subset subset
    simp only [List.length_range,full] at bound
    omega

theorem ancestor_root (tree : TraversalTree) (forest : Forest tree)
    (current root : Nat) (valid : current < tree.nodes.size)
    (uniqueRoot : ∀ index, index < tree.nodes.size → (nodeData tree index).parent = none → index = root) :
    (tree.ancestorPath current).getLast! = root := by
  have nonempty : tree.ancestorPath current ≠ [] := ancestors_nonempty tree tree.nodes.size current
  have lastMember : (tree.ancestorPath current).getLast! ∈ tree.ancestorPath current := by
    rw [List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty]
    exact List.getLast_mem nonempty
  have lastBound := (ancestors_data tree forest.rank forest.parents tree.nodes.size current valid).2 _ lastMember
  exact uniqueRoot _ lastBound.1 (ancestor_terminal tree forest current valid)
theorem ancestor_root_present (tree : TraversalTree) (forest : Forest tree)
    (present : Nat → Prop) (closed : ParentClosed tree present)
    (current root : Nat) (valid : current < tree.nodes.size) (initial : present current)
    (uniqueRoot : ∀ index, index < tree.nodes.size → present index →
      (nodeData tree index).parent = none → index = root) :
    (tree.ancestorPath current).getLast! = root := by
  have nonempty : tree.ancestorPath current ≠ [] := ancestors_nonempty tree tree.nodes.size current
  have lastMember : (tree.ancestorPath current).getLast! ∈ tree.ancestorPath current := by
    rw [List.getLast!_eq_getLast?_getD,List.getLast?_eq_some_getLast nonempty]
    exact List.getLast_mem nonempty
  have lastBound := (ancestors_data tree forest.rank forest.parents tree.nodes.size current valid).2 _ lastMember
  have lastPresent := ancestors_present tree present closed tree.nodes.size current initial _ lastMember
  exact uniqueRoot _ lastBound.1 lastPresent (ancestor_terminal tree forest current valid)

end DuplicatePrefix.GeneralBorrowTerminal

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowTerminal." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic terminal-root dependency {dependency}"
