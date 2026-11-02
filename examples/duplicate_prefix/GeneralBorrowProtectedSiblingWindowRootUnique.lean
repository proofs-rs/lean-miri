import duplicate_prefix.GeneralBorrowProtectedSiblingWindowLifetimes
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowRootUnique
import duplicate_prefix.GeneralBorrowProtectedSiblingRootUniqueHistory
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingWindowRootUnique
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedReleaseHistory GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- The original root retains its stored Unique permission through the actual
allocation, every generated protected sibling and selected exposure, and every
ordered protector release. No intermediate ownership or Unique premise is used. -/
theorem formed (capacity : UInt64) (nonzero : capacity ≠ 0) (selected : List Bool) (room : selected.length+2 ≤ 4294967295) :
    match GeneralBorrowProtectedSiblingWindowLifetimes.operation capacity selected with
    | .error _ => False
    | .ok output =>
      Every (GeneralBorrowConstructorPriorPermission.At GeneralBorrowFullSharedSeed.root (some .Unique)) output.tree.locations ∧
      Every (GeneralBorrowProtectedReadRelease.Profile output.tree output.generated.global.protectedTags) output.tree.locations := by
  obtain ⟨ready⟩ := GeneralBorrowProtectedSiblingGenerationWindow.generate capacity nonzero selected room
  have mapped : Tags ready.input.tree ready.state.global.protectedTags ready.state.tags := by
    intro tag member
    obtain ⟨index,node,present,tagged,lookup⟩ := ready.mapped tag member
    exact ⟨index,node,present,lookup,tagged,ready.held tag member⟩
  have initialUnique := GeneralBorrowProtectedSiblingGenerationWindowRootUnique.formed capacity nonzero selected room ready
  have fits : ready.input.tree.nodes.data.size ≤ 4294967296 := by have aligned := ready.input.aligned;have room := ready.input.fits;omega
  have unique := GeneralBorrowProtectedSiblingRootUniqueHistory.unique ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.input.parentNode ready.input.parentPresent ready.readable initialUnique
  have readable := GeneralBorrowProtectedReleaseHistory.run ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    fits ready.input.depth ready.input.children ready.roots ready.input.covered mapped ready.readable
  simp only [GeneralBorrowProtectedSiblingWindowLifetimes.operation,ready.actual,Except.bind,bind,pure,Except.pure]
  rw [←ready.tree]
  rw [ready.parent] at unique
  exact ⟨unique,readable.2.2⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingWindowRootUnique
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingWindowRootUnique.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated final rootUnique dependency {dependency}"
