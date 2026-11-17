import duplicate_prefix.GeneralBorrowFreshLocation
namespace DuplicatePrefix.GeneralBorrowFreshDeassignment
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

elab "source_remove_useless_node" : term => do
  let candidates := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.removeUselessNode" then some name else none
  match candidates with
  | [name] => return mkConst name
  | _ => throwError "expected pinned source node-removal helper"
elab "unfold_source_remove_useless_node" : tactic => do
  let candidates := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.removeUselessNode" then some name else none
  match candidates with
  | [name] => let name := mkIdent name;evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected pinned source node-removal helper"

/-- Actual sparse removal clears a slot even when the sparse permission map
has a different length from the node table. -/
theorem get_removed {α : Type} (map : UniValMap α) (index : UniIndex) : (map.remove index).get index = none := by
  unfold UniValMap.remove UniValMap.get
  by_cases valid : index.toNat < map.data.size
  · simp [valid,Array.getElem?_set]
  · simp [valid,Array.getElem?_eq_none (by omega : map.data.size ≤ index.toNat)]

/-- The exact production GC/deassignment primitive clears the node and every
per-location permission slot, not only currently borrowed slices. Therefore
future reuse does not inherit accessed permissions outside its new slice.
The caller must separately justify GC eligibility and tag/index consistency. -/
theorem removed_clean (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) :
    let result := source_remove_useless_node tree index
    result.2 = .ok () ∧ result.1.nodes.get index = none ∧
      ∀ position (valid : position < result.1.locations.entries.size),
        result.1.locations.entries[position].data.perms.get index = none := by
  unfold_source_remove_useless_node
  simp only [present,Id.run,bind,pure]
  refine ⟨True.intro,get_removed tree.nodes index,?_⟩
  intro position valid
  simpa only [Miri.DataStructures.DedupRangeMap.modifyAll,Array.getElem_map] using
    get_removed (tree.locations.entries[position]'(by simpa only [Miri.DataStructures.DedupRangeMap.modifyAll,Array.size_map] using valid)).data.perms index
end DuplicatePrefix.GeneralBorrowFreshDeassignment
#print axioms DuplicatePrefix.GeneralBorrowFreshDeassignment.removed_clean
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshDeassignment." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved sparse deassignment dependency {dependency}"
