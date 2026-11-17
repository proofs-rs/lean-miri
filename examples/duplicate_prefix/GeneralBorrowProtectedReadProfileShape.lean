import duplicate_prefix.GeneralBorrowProtectedReadShape
import duplicate_prefix.GeneralBorrowProtectedReadRelease
namespace DuplicatePrefix.GeneralBorrowProtectedReadProfileShape
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralBorrowFreshOwnership
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
theorem shape (before after : BorrowTree) (protections : ProtectedTags) (same : treeShape after = treeShape before)
    (initial : Every (GeneralBorrowProtectedReadRelease.Profile before protections) before.locations) :
    Every (GeneralBorrowProtectedReadRelease.Profile after protections) after.locations := by
  have nodes := congrArg (fun row => row.2.1) same
  have rows := congrArg (fun row => row.2.2.1) same
  change after.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) = before.locations.entries.map (fun segment => (segment.range,locationShape segment.data)) at rows
  change after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) at nodes
  have sizes : after.locations.entries.size = before.locations.entries.size := by
    simpa only [normalShape,Array.size_map] using congrArg Array.size rows
  intro position valid
  have oldValid : position < before.locations.entries.size := by omega
  have row := congrArg (fun entries => entries[position]?) rows
  simp only [Array.getElem?_map,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem oldValid,Option.map_some] at row
  have pair := Prod.mk.inj (Option.some.inj row)
  have projection := projection_shape before after _ _ protections nodes pair.2
  obtain ⟨⟨forest⟩,data⟩ := initial position oldValid
  refine ⟨⟨?_⟩,GeneralBorrowProtectedReadShape.normal _ _ projection data⟩
  have topology := congrArg (fun row => row.1) projection
  change (source_normal_projection after after.locations.entries[position].data protections).topology =
    (source_normal_projection before before.locations.entries[position].data protections).topology at topology
  rw [topology]
  exact forest
end DuplicatePrefix.GeneralBorrowProtectedReadProfileShape
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedReadProfileShape.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected readable profile shape dependency {dependency}"
