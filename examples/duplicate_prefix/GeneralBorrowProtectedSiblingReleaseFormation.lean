import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseStable
import duplicate_prefix.GeneralBorrowConstructorPriorPermission
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseFormation
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseStable
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Source-derived sibling descriptors and their stored conflict facts imply the
prior-tag condition used by the actual release/cache loop, regardless of which
nodes were selected for exposure. -/
theorem stable (tree : BorrowTree) (tags : List BorTag)
    (nodeTags : ∀ index node,tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (conflicted : ∀ tag ∈ tags,∃ index,tree.indexOfTag tag = some index ∧
      Every (GeneralBorrowConstructorPriorPermission.At index (some (.ReservedFrz true))) tree.locations) :
    Every (ForTags tags tree) tree.locations := by
  intro position valid query node present _exposed member
  obtain ⟨index,lookup,permission⟩ := conflicted node.tag member
  have same : index = query := Option.some.inj (lookup.symm.trans (nodeTags query node present))
  subst index
  have stored := permission position valid
  unfold GeneralBorrowConstructorPriorPermission.At at stored
  cases found : (tree.locations.entries[position].data.perms.get query) with
  | none => simp [found] at stored
  | some state =>
    have equal : state.permission = .ReservedFrz true := by simpa [found] using stored
    exact Or.inl (by simpa [found] using equal)
end DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseFormation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingReleaseFormation.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved sibling release formation dependency {dependency}"
