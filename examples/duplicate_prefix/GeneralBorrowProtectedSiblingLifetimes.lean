import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationComplete
import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseHistory
import duplicate_prefix.GeneralBorrowProtectedSiblingReleaseFormation
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingLifetimes
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedSiblingGeneration GeneralBorrowProtectedSiblingGenerationCore
open GeneralBorrowProtectedReleaseHistory GeneralBorrowProtectedLifetimeSeed GeneralRangeMapState GeneralBorrowExposureCardinality
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

structure Output where
  generated : Snapshot
  tree : BorrowTree
  ended : GlobalState

/-- Actual root allocation, selected protected sibling constructors/exposures,
source-order full-table releases, and only then actual endCall. -/
def operation (selected : List Bool) : Except GlobalStateError Output := do
  let state ← GeneralBorrowProtectedSiblingGeneration.operation selected
  pure ⟨state,execute state.tree state.global.protectedTags state.tags,state.global.endCall state.frame⟩

/-- Every finite one-byte schedule within numeric headroom completes its actual
ordered release history and ends with a coherent cache under the real endCall
table. The final sibling may be exposed while still unconflicted. This source
protocol theorem does not assert arbitrary Rust/MIR reachability or safety. -/
theorem completes (selected : List Bool) (room : selected.length+2 ≤ 4294967295) :
    match operation selected with
    | .error _ => False
    | .ok output =>
      output.generated.tags.length = selected.length ∧
      AllReleased output.generated.tree output.generated.global.protectedTags output.generated.tags ∧
      Every (fun location => LocationCoherent output.tree location output.ended.protectedTags) output.tree.locations := by
  let initial := seed selected.length room
  obtain ⟨after,actual,count⟩ := GeneralBorrowProtectedSiblingGenerationComplete.run selected initial
  have operationEq : GeneralBorrowProtectedSiblingGeneration.operation selected = .ok (snapshot after) := by
    simp only [GeneralBorrowProtectedSiblingGeneration.operation,root_allocation,Except.bind,bind,pure,Except.pure]
    exact actual
  have mapped : Tags after.input.tree after.global.protectedTags after.tags := by
    intro tag member
    obtain ⟨descriptor⟩ := after.descriptors tag member
    exact ⟨descriptor.index,descriptor.node,descriptor.present,by
      have lookup := after.allocator.nodeTags descriptor.index descriptor.node descriptor.present
      simpa only [BorrowTree.indexOfTag,descriptor.tagged] using lookup,descriptor.tagged,after.held tag member⟩
  have earlier : ∀ tag ∈ after.tags.dropLast,∃ index,after.input.tree.indexOfTag tag = some index ∧
      Every (GeneralBorrowConstructorPriorPermission.At index (some (.ReservedFrz true))) after.input.tree.locations := by
    intro tag member
    rcases after.earlier with empty | ⟨past,last,index,split,found,typed,previous⟩
    · rw [empty] at member;simp at member
    · exact previous tag (by simpa [split] using member)
  have stable := GeneralBorrowProtectedSiblingReleaseFormation.stable after.input.tree after.tags.dropLast after.allocator.nodeTags earlier
  have fits : after.input.tree.nodes.data.size ≤ 4294967296 := by have aligned := after.input.aligned;have room := after.input.fits;omega
  have history := GeneralBorrowProtectedSiblingReleaseHistory.complete after.input.tree after.global.protectedTags after.tags after.input.parent
    after.distinct fits after.input.depth after.input.children after.roots after.input.covered after.allocator.nodeTags mapped after.readable after.coherent stable
  have cleanup := GeneralBorrowProtectedReleaseCacheHistory.pending_end_call after.global after.frame allocation after.tags
    (by rw [after.frameTags])
  have finalCache := history.2
  rw [←cleanup] at finalCache
  simp only [operation,operationEq,Except.bind,bind,pure,Except.pure]
  refine ⟨?_,history.1,finalCache⟩
  change after.tags.length = selected.length
  have zero : initial.tags = [] := rfl
  simpa only [zero,List.length_nil,Nat.zero_add] using count
end DuplicatePrefix.GeneralBorrowProtectedSiblingLifetimes
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingLifetimes.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated sibling lifecycle dependency {dependency}"
