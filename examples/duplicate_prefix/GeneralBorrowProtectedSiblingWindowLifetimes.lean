import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowComplete
import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseHistory
import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseFormation
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingWindowLifetimes
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGenerationWindow GeneralBorrowProtectedSiblingGenerationWindowCore
open GeneralBorrowProtectedReleaseHistory GeneralBorrowProtectedLifetimeSeed GeneralRangeMapState GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

structure Output where
  generated : Snapshot
  tree : BorrowTree
  ended : GlobalState

/-- Actual root allocation, selected protected sibling constructors/exposures,
source-order full-table releases, and only then actual endCall. -/
def operation (capacity : UInt64) (selected : List Bool) : Except GlobalStateError Output := do
  let state ← GeneralBorrowProtectedSiblingGenerationWindow.operation capacity selected
  pure ⟨state,execute state.tree state.global.protectedTags state.tags,state.global.endCall state.frame⟩

/-- Every finite positive-capacity full-window schedule within numeric headroom completes its actual
ordered release history and ends with a coherent cache under the real endCall
table. The final sibling may be exposed while still unconflicted. This source
protocol theorem does not assert arbitrary Rust/MIR reachability or safety. -/
theorem completes (capacity : UInt64) (nonzero : capacity ≠ 0) (selected : List Bool) (room : selected.length+2 ≤ 4294967295) :
    match operation capacity selected with
    | .error _ => False
    | .ok output =>
      output.generated.tags.length = selected.length ∧
      AllReleased output.generated.tree output.generated.global.protectedTags output.generated.tags ∧
      Every (fun location => LocationCoherent output.tree location output.ended.protectedTags) output.tree.locations := by
  obtain ⟨ready⟩ := GeneralBorrowProtectedSiblingGenerationWindow.generate capacity nonzero selected room
  have mapped : Tags ready.input.tree ready.state.global.protectedTags ready.state.tags := by
    intro tag member
    obtain ⟨index,node,present,tagged,lookup⟩ := ready.mapped tag member
    exact ⟨index,node,present,lookup,tagged,ready.held tag member⟩
  have stable := GeneralBorrowProtectedSiblingReleaseFormation.stable ready.input.tree ready.state.tags.dropLast ready.allocator.nodeTags ready.earlier
  have fits : ready.input.tree.nodes.data.size ≤ 4294967296 := by have aligned := ready.input.aligned;have room := ready.input.fits;omega
  have history := GeneralBorrowProtectedSiblingReleaseHistory.complete ready.input.tree ready.state.global.protectedTags ready.state.tags ready.input.parent
    ready.distinct fits ready.input.depth ready.input.children ready.roots ready.input.covered ready.allocator.nodeTags mapped ready.readable ready.coherent stable
  have cleanup := GeneralBorrowProtectedReleaseCacheHistory.pending_end_call ready.state.global ready.state.frame allocation ready.state.tags
    (by simp [ready.frame,GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation,GeneralBorrowProtectedLifetimeSeed.allocation])
  have finalCache := history.2
  rw [←cleanup] at finalCache
  simp only [operation,ready.actual,Except.bind,bind,pure,Except.pure]
  rw [←ready.tree]
  refine ⟨?_,history.1,finalCache⟩
  exact ready.count

end DuplicatePrefix.GeneralBorrowProtectedSiblingWindowLifetimes
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingWindowLifetimes.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated sibling lifecycle dependency {dependency}"
