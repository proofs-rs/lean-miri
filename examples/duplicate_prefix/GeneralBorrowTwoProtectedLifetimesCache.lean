import duplicate_prefix.GeneralBorrowTwoProtectedCacheReady
import duplicate_prefix.GeneralBorrowTwoProtectedLifetimes
import duplicate_prefix.GeneralBorrowProtectedReleaseCacheHistory
namespace DuplicatePrefix.GeneralBorrowTwoProtectedLifetimesCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProtectedLifetimeSeed DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralBorrowProtectedReleaseHistory
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- The exact source-generated canonical two-lifetime cycle finishes with
coherent counters under the real endCall table. Its earlier exposed reservation
is first conflicted by the actual later leading Read. Pending releases use a
separate virtual-table invariant; coherence under the full still-held table is
never substituted after the first exposure-release adjustment. Together with
GeneralBorrowTwoProtectedLifetimes.completes this certifies the operation's
actual statuses and final cache, not all-input whole-MIR safety. -/
theorem coherent : match GeneralBorrowTwoProtectedLifetimes.operation with
    | .error _ => False
    | .ok output => Every (fun location => LocationCoherent output.secondRelease.tree location output.ended.protectedTags)
        output.secondRelease.tree.locations := by
  obtain ⟨ready⟩ := GeneralBorrowTwoProtectedCacheReady.generate
  have stable : Every (GeneralBorrowProtectedReadStable.AllExposed ready.second.child.tree) ready.second.child.tree.locations := by
    intro position valid query node present exposed
    have tag : node.tag = tag2 := ready.onlyExposed query node present exposed
    have lookup := ready.nodeTags query node present
    rw [tag,ready.firstLookup] at lookup
    have same : query = ready.firstIndex := (Option.some.inj lookup).symm
    subst query
    have conflict := ready.firstConflicted position valid
    cases stored : ready.second.child.tree.locations.entries[position].data.perms.get ready.firstIndex with
    | none =>
      simp only [GeneralBorrowConstructorPriorPermission.At,stored,Option.map_none] at conflict
      cases conflict
    | some state =>
      simp only [GeneralBorrowConstructorPriorPermission.At,stored,Option.map_some,Option.some.injEq] at conflict
      simp only [stored,Option.getD_some]
      exact Or.inl conflict
  have firstHeld : ready.second.global.protectedTags.contains tag2 = true := by
    rw [ready.tags]
    simp only [ProtectedTags.contains,GeneralBorrowProtectorCacheMap.insert_other _ tag3 tag2 .StrongProtector (by decide),
      ProtectedTags.get_insert_same,Option.isSome_some]
  have secondHeld : ready.second.global.protectedTags.contains tag3 = true := by
    rw [ready.tags]
    simp only [ProtectedTags.contains,ProtectedTags.get_insert_same,Option.isSome_some]
  have mapped : Tags ready.second.child.tree ready.second.global.protectedTags [tag2,tag3] := by
    intro tag member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same
    · subst tag;exact ⟨ready.firstIndex,ready.firstNode,ready.firstPresent,ready.firstLookup,ready.firstNodeTag,firstHeld⟩
    · subst tag;exact ⟨ready.secondIndex,ready.secondNode,ready.secondPresent,ready.secondLookup,ready.secondNodeTag,secondHeld⟩
  have held : ∀ tag ∈ [tag2,tag3],ready.second.global.protectedTags.contains tag = true := by
    intro tag member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same | same
    · subst tag;exact firstHeld
    · subst tag;exact secondHeld
  have history := GeneralBorrowProtectedReleaseCacheHistory.run ready.second.child.tree ready.second.global.protectedTags
    ready.second.global.protectedTags [tag2,tag3] GeneralBorrowFullSharedSeed.root (by decide) ready.fits ready.depth
    ready.children ready.roots ready.covered ready.nodeTags mapped held ready.profile ready.coherent stable
  have cleanup := GeneralBorrowProtectedReleaseCacheHistory.pending_end_call ready.second.global ready.second.frame allocation [tag2,tag3]
    (by rw [ready.frame];rfl)
  have finalCache := history.2.2.2.1
  rw [←cleanup] at finalCache
  let firstRelease := ready.second.child.tree.releaseProtector ready.first.tag ready.second.global.protectedTags
  let secondRelease := firstRelease.tree.releaseProtector ready.second.tag ready.second.global.protectedTags
  have finalTree : execute ready.second.child.tree ready.second.global.protectedTags [tag2,tag3] = secondRelease.tree := by
    change execute ready.second.child.tree ready.second.global.protectedTags [tag2,tag3] =
      ((ready.second.child.tree.releaseProtector ready.first.tag ready.second.global.protectedTags).tree.releaseProtector ready.second.tag ready.second.global.protectedTags).tree
    rw [ready.firstTag,ready.secondTag]
    rfl
  rw [finalTree] at finalCache
  let output : GeneralBorrowTwoProtectedLifetimes.Output :=
    ⟨BorTag.one,initial,ready.first,ready.exposed,ready.second,firstRelease,secondRelease,ready.second.global.endCall ready.second.frame⟩
  have actual : GeneralBorrowTwoProtectedLifetimes.operation = .ok output := by
    simp only [GeneralBorrowTwoProtectedLifetimes.operation,root_allocation,Except.bind,Except.pure,bind,pure]
    change (do
      let first ← GeneralBorrowForestFnEntry.operation initial global {} allocation BorTag.one 0 1 .VisitChildrenOfAccessed
      let exposed := first.child.tree.exposeTag first.global.protectedTags first.tag
      let second ← GeneralBorrowForestFnEntry.operation exposed.tree first.global first.frame allocation BorTag.one 0 1 .VisitChildrenOfAccessed
      pure (⟨BorTag.one,initial,first,exposed,second,
        second.child.tree.releaseProtector first.tag second.global.protectedTags,
        (second.child.tree.releaseProtector first.tag second.global.protectedTags).tree.releaseProtector second.tag second.global.protectedTags,
        second.global.endCall second.frame⟩ : GeneralBorrowTwoProtectedLifetimes.Output)) = .ok output
    rw [ready.firstEq]
    simp only [Except.bind,bind,pure]
    rw [ready.exposedEq,ready.secondEq]
    rfl
  rw [actual]
  exact finalCache
/-- One no-premise endpoint for every real operation status, chronological
protector bookkeeping and final cache coherence of this generated cycle. -/
theorem completes : match GeneralBorrowTwoProtectedLifetimes.operation with
    | .error _ => False
    | .ok output =>
      (output.first.access.status = .Completed ∧ output.first.child.outcome = .ok () ∧
      output.exposed.outcome = .ok () ∧
      output.second.access.status = .Completed ∧ output.second.child.outcome = .ok () ∧
      output.firstRelease.status = .Released ∧ output.secondRelease.status = .Released ∧
      output.second.frame.protectedTags = #[(allocation,output.first.tag),(allocation,output.second.tag)] ∧
      output.second.global.protectedTags.contains output.first.tag = true ∧
      output.second.global.protectedTags.contains output.second.tag = true ∧
      output.ended.protectedTags = {}) ∧
      Every (fun location => LocationCoherent output.secondRelease.tree location output.ended.protectedTags)
        output.secondRelease.tree.locations := by
  have statuses := GeneralBorrowTwoProtectedLifetimes.completes
  have cache := coherent
  cases actual : GeneralBorrowTwoProtectedLifetimes.operation with
  | error error => simpa only [actual] using statuses
  | ok output => exact ⟨by simpa only [actual] using statuses,by simpa only [actual] using cache⟩

end DuplicatePrefix.GeneralBorrowTwoProtectedLifetimesCache
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoProtectedLifetimesCache.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated two protected lifetime cache dependency {dependency}"
