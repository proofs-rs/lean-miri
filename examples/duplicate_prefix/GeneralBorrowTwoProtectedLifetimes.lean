import duplicate_prefix.GeneralBorrowTwoProtectedReadableReady
namespace DuplicatePrefix.GeneralBorrowTwoProtectedLifetimes
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProtectedLifetimeSeed
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

structure Output where
  rootTag : BorTag
  initial : BorrowTree
  first : GeneralBorrowForestFnEntry.Output
  exposed : BorrowTree.TreeMutationResult
  second : GeneralBorrowForestFnEntry.Output
  firstRelease : BorrowTree.ProtectorReleaseResult
  secondRelease : BorrowTree.ProtectorReleaseResult
  ended : GlobalState

/-- Two real pointer allocations and Strong registrations in one frame, with
actual overlapping one-byte Default constructors and exposure of the earlier
child before the later leading Read. Both releases retain the entire global
table; the owning frame's endCall occurs only after both release scans. -/
def operation : Except GlobalStateError Output := do
  let (global,rootTag) ← GlobalState.new.rootPointerTag allocation
  let initial := BorrowTree.new rootTag (Size.ofBytes 1)
  let first ← GeneralBorrowForestFnEntry.operation initial global {} allocation rootTag 0 1 .VisitChildrenOfAccessed
  let exposed := first.child.tree.exposeTag first.global.protectedTags first.tag
  let second ← GeneralBorrowForestFnEntry.operation exposed.tree first.global first.frame allocation rootTag 0 1 .VisitChildrenOfAccessed
  let firstRelease := second.child.tree.releaseProtector first.tag second.global.protectedTags
  let secondRelease := firstRelease.tree.releaseProtector second.tag second.global.protectedTags
  pure ⟨rootTag,initial,first,exposed,second,firstRelease,secondRelease,second.global.endCall second.frame⟩

/-- Actual source-loop completion of the fully generated two-lifetime cycle.
This finite one-byte BorrowTree protocol is not an all-input whole-MIR theorem.
No initial or intermediate tree, successful operation, permission/cache profile,
registration result or release result is supplied by the caller. -/
theorem completes : match operation with
    | .error _ => False
    | .ok output =>
      output.first.access.status = .Completed ∧ output.first.child.outcome = .ok () ∧
      output.exposed.outcome = .ok () ∧
      output.second.access.status = .Completed ∧ output.second.child.outcome = .ok () ∧
      output.firstRelease.status = .Released ∧ output.secondRelease.status = .Released ∧
      output.second.frame.protectedTags = #[(allocation,output.first.tag),(allocation,output.second.tag)] ∧
      output.second.global.protectedTags.contains output.first.tag = true ∧
      output.second.global.protectedTags.contains output.second.tag = true ∧
      output.ended.protectedTags = {} := by
  obtain ⟨ready⟩ := GeneralBorrowTwoProtectedReadableReady.generate
  have firstHeld : ready.second.global.protectedTags.contains tag2 = true := by
    rw [ready.tags]
    simp only [ProtectedTags.contains,GeneralBorrowProtectorCacheMap.insert_other _ tag3 tag2 .StrongProtector (by decide),
      ProtectedTags.get_insert_same,Option.isSome_some]
  have secondHeld : ready.second.global.protectedTags.contains tag3 = true := by
    rw [ready.tags]
    simp only [ProtectedTags.contains,ProtectedTags.get_insert_same,Option.isSome_some]
  have releasedFirst := GeneralBorrowProtectedReadReleaseExposed.release ready.second.child.tree ready.second.global.protectedTags
    ready.firstIndex GeneralBorrowFullSharedSeed.root ready.firstNode ready.firstPresent
    (by rw [ready.firstNodeTag];exact ready.firstLookup) (by rw [ready.firstNodeTag];exact firstHeld)
    ready.fits ready.depth ready.children ready.roots ready.covered ready.profile
  rw [ready.firstNodeTag] at releasedFirst
  let firstRelease := ready.second.child.tree.releaseProtector ready.first.tag ready.second.global.protectedTags
  have firstComplete : firstRelease.status = .Released := by simpa only [firstRelease,ready.firstTag] using releasedFirst.1
  have firstFrame : firstRelease.tree = {ready.second.child.tree with locations := firstRelease.tree.locations} := by
    simpa only [firstRelease,ready.firstTag] using releasedFirst.2.1
  have firstProfile : GeneralRangeMapState.Every (GeneralBorrowProtectedReadRelease.Profile firstRelease.tree ready.second.global.protectedTags)
      firstRelease.tree.locations := by
    simpa only [firstRelease,ready.firstTag] using releasedFirst.2.2
  have nodes : firstRelease.tree.nodes = ready.second.child.tree.nodes := by simpa only using congrArg BorrowTree.nodes firstFrame
  have releasedSecond := GeneralBorrowProtectedReadReleaseExposed.release firstRelease.tree ready.second.global.protectedTags
    ready.secondIndex GeneralBorrowFullSharedSeed.root ready.secondNode
    (by rw [firstFrame];exact ready.secondPresent) (by rw [firstFrame,ready.secondNodeTag];exact ready.secondLookup)
    (by rw [ready.secondNodeTag];exact secondHeld) (by rw [nodes];exact ready.fits)
    (GeneralBorrowFreshReadFrame.depth_on ready.second.child.tree firstRelease.tree nodes ready.depth)
    (by rw [firstFrame];exact ready.children) (by rw [firstFrame];exact ready.roots)
    (by rw [firstFrame];exact ready.covered) firstProfile
  rw [ready.secondNodeTag] at releasedSecond
  let secondRelease := firstRelease.tree.releaseProtector ready.second.tag ready.second.global.protectedTags
  have secondComplete : secondRelease.status = .Released := by simpa only [secondRelease,ready.secondTag] using releasedSecond.1
  have ended : (ready.second.global.endCall ready.second.frame).protectedTags = {} := by
    change (ready.second.frame.protectedTags.foldl (fun tags pair => tags.remove pair.2) ready.second.global.protectedTags) = {}
    rw [ready.frame,ready.tags]
    decide +kernel
  let output : Output := ⟨BorTag.one,initial,ready.first,ready.exposed,ready.second,firstRelease,secondRelease,
    ready.second.global.endCall ready.second.frame⟩
  have actual : operation = .ok output := by
    simp only [operation,root_allocation,Except.bind,Except.pure,bind,pure]
    change (do
      let first ← GeneralBorrowForestFnEntry.operation initial global {} allocation BorTag.one 0 1 .VisitChildrenOfAccessed
      let exposed := first.child.tree.exposeTag first.global.protectedTags first.tag
      let second ← GeneralBorrowForestFnEntry.operation exposed.tree first.global first.frame allocation BorTag.one 0 1 .VisitChildrenOfAccessed
      pure (⟨BorTag.one,initial,first,exposed,second,
        second.child.tree.releaseProtector first.tag second.global.protectedTags,
        (second.child.tree.releaseProtector first.tag second.global.protectedTags).tree.releaseProtector second.tag second.global.protectedTags,
        second.global.endCall second.frame⟩ : Output)) = .ok output
    rw [ready.firstEq]
    simp only [Except.bind,bind,pure]
    rw [ready.exposedEq,ready.secondEq]
    rfl
  rw [actual]
  refine ⟨ready.firstRead,ready.firstChild,ready.exposedOK,ready.secondRead,ready.secondChild,firstComplete,secondComplete,?_,?_,?_,ended⟩
  · simpa only [output,ready.firstTag,ready.secondTag] using ready.frame
  · simpa only [output,ready.firstTag] using firstHeld
  · simpa only [output,ready.secondTag] using secondHeld
end DuplicatePrefix.GeneralBorrowTwoProtectedLifetimes
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoProtectedLifetimes.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved two protected lifetimes dependency {dependency}"
