import duplicate_prefix.GeneralBorrowProtectedSiblingWindowRootUnique
import duplicate_prefix.GeneralBorrowProtectedSiblingWindowTable
import duplicate_prefix.GeneralBorrowProtectedSiblingRootOwned
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingWindowRootOwned
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedReleaseHistory GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Actual generated lifetimes restore original-root Write ownership after all
source releases and endCall. All root permission, graph and empty-protector facts
come from the real generated history; arbitrary exposure selections are allowed. -/
theorem formed (capacity : UInt64) (nonzero : capacity ≠ 0) (selected : List Bool) (room : selected.length+2 ≤ 4294967295) :
    match GeneralBorrowProtectedSiblingWindowLifetimes.operation capacity selected with
    | .error _ => False
    | .ok output => Every (GeneralBorrowRange.LocationOwned output.tree output.ended.protectedTags GeneralBorrowFullSharedSeed.root .Write) output.tree.locations := by
  obtain ⟨ready⟩ := GeneralBorrowProtectedSiblingGenerationWindow.generate capacity nonzero selected room
  have mapped : Tags ready.input.tree ready.state.global.protectedTags ready.state.tags := by
    intro tag member
    obtain ⟨index,node,present,tagged,lookup⟩ := ready.mapped tag member
    exact ⟨index,node,present,lookup,tagged,ready.held tag member⟩
  have initialUnique := GeneralBorrowProtectedSiblingGenerationWindowRootUnique.formed capacity nonzero selected room ready
  have fits : ready.input.tree.nodes.data.size ≤ 4294967296 := by have aligned := ready.input.aligned;have room := ready.input.fits;omega
  have unique := GeneralBorrowProtectedSiblingRootUniqueHistory.unique ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.input.parentNode ready.input.parentPresent ready.readable initialUnique
  have history := GeneralBorrowProtectedReleaseHistory.run ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.readable
  have cleanup := GeneralBorrowProtectedSiblingWindowTable.formed capacity nonzero selected room
  simp only [GeneralBorrowProtectedSiblingWindowLifetimes.operation,ready.actual,Except.bind,bind,pure,Except.pure] at cleanup ⊢
  rw [←ready.tree]
  rw [cleanup,←ready.parent]
  let finalTree := execute ready.input.tree ready.state.global.protectedTags ready.state.tags
  have frame : finalTree = {ready.input.tree with locations := finalTree.locations} := history.2.1
  have depth : GeneralBorrowExposure.ParentDepth finalTree.nodes := by rw [frame];exact ready.input.depth
  have present : finalTree.nodeAt ready.input.parent = some ready.input.parentNode := by rw [frame];exact ready.input.parentPresent
  have roots : finalTree.roots = #[ready.input.parent] := by rw [frame];exact ready.roots
  have covered : GeneralBorrowGraph.RootsCover finalTree := by rw [frame];exact ready.input.covered
  intro position valid
  exact GeneralBorrowProtectedSiblingRootOwned.location finalTree _ ready.state.global.protectedTags ready.input.parent ready.input.parentNode present roots covered depth
    (history.2.2 position valid) (unique position valid)
end DuplicatePrefix.GeneralBorrowProtectedSiblingWindowRootOwned
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingWindowRootOwned.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated root ownership dependency {dependency}"
