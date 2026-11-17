import duplicate_prefix.ProtectedStages
import duplicate_prefix.ProtectedRelease
namespace DuplicatePrefix.FourNodeRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess RangeMapNonempty NestedBorrowAccess NestedConstruction NestedTransitions MixedRelease ProtectedStages
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

theorem normal_outer :
    (normal4 true false).performAccess 1 .Read .SkipChildrenOfAccessed =
      ⟨normal4 true false,0,[⟨1,.LocalAccess⟩,⟨0,.LocalAccess⟩],.Completed⟩ := by decide +kernel

private theorem loop_yield {β : Type} (f : Unit → β → Id (ForInStep β))
    (initial next : β) (step : f () initial = .yield next) :
    Lean.Loop.forIn {} initial f = Lean.Loop.forIn {} next f := by
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [step,bind,pure]

theorem outer_min_exposed (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) :
    source_min_exposed (tree4 tags locations) ⟨1⟩ = none := by
  unfold_min_exposed
  simp only [Id.run,bind,pure,ForIn.forIn,Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have step0 : scan () (none,#[⟨1⟩],0,none) = .yield (none,#[⟨2⟩],1,none) := by
    simp [scan,UniValMap.size,UniValMap.get,UniIndex.toNat,bind,pure,← Array.forIn_toList]
  have step1 : scan () (none,#[⟨2⟩],1,none) = .yield (none,#[⟨3⟩],2,none) := by
    simp [scan,UniValMap.size,UniValMap.get,UniIndex.toNat,bind,pure,← Array.forIn_toList]
  have step2 : scan () (none,#[⟨3⟩],2,none) = .yield (none,#[],3,none) := by
    simp [scan,UniValMap.size,UniValMap.get,UniIndex.toNat,bind,pure,← Array.forIn_toList]
  have last : scan () (none,#[],3,none) = .done (none,#[],3,none) := by
    simp [scan,UniValMap.size,bind,pure]
  rw [loop_yield scan _ _ step0,loop_yield scan _ _ step1]
  have final := RangeMapNonempty.loop_one_update scan _ _ step2 last
  simp [final,bind,pure]

abbrev outerAccess (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree)
    (protections : ProtectedTags) (range : ByteRange) :=
  source_tree_access_at (tree4 tags locations) (location4 true) (some ⟨1⟩) .Read
    protections .SkipChildrenOfAccessed range

theorem outer_access_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (protections : ProtectedTags) (range : ByteRange) (mask : StageMask tags protections 4 false) :
    source_access_location (outerAccess tags locations protections range) = location4 true ∧
    source_access_status (outerAccess tags locations protections range) = none := by
  unfold outerAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, projection4 tags locations protections mask,
    show (⟨1⟩ : UniIndex).toNat = 1 from rfl, normal_outer]
  simp [tree4, stageNode, location3, location4, location5, normal3, normal4, normal5,
    mutableNone, mutableRead, frozenRead, frozenNone, min_exposed4, outer_min_exposed,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  simp [min_exposed4, outer_min_exposed, Id.run, UniIndex.toNat, UniIndex.ofNat?, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

theorem outer_index (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (tree4 tags locations).indexOfTag (tags 1) = some ⟨1⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp only [BorrowTree.indexOfTag, tree4, UniKeyMap.get]
  rw [← Array.find?_toList]
  simp [eqTags]

theorem outer_exposure_release (tags : Fin 6 → BorTag)
    (locations : DedupRangeMap LocationTree) (distinct : Function.Injective tags) :
    (tree4 tags locations).updateExposureForProtectorRelease (tags 1) =
      ⟨tree4 tags locations, .ok ()⟩ := by
  unfold BorrowTree.updateExposureForProtectorRelease
  dsimp only
  rw [outer_index tags distinct locations]
  simp [BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, pure]

theorem outer_release_single (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : StageMask tags protections 4 false) (before after : Option ByteRange)
    (source : ByteRange) (distinct : Function.Injective tags) :
    let segments := #[⟨source, location4 true⟩]
    let locations := withOutside before after segments
    (tree4 tags locations).releaseProtector (tags 1) (protections) =
      ⟨tree4 tags locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    #[⟨source, location4 true⟩]
  have readLocation (range : ByteRange) :=
    (outer_access_local tags distinct locations protections range mask).1
  have readStatus (range : ByteRange) :=
    (outer_access_local tags distinct locations protections range mask).2
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [outerAccess] at readLocation readStatus
  change (tree4 tags locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [outer_index tags distinct locations]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases before <;> cases after
  all_goals
    first
    | have locSize : locations.entries.size = 1 := by simp [locations, withOutside]
    | have locSize : locations.entries.size = 2 := by simp [locations, withOutside]
    | have locSize : locations.entries.size = 3 := by simp [locations, withOutside]
    simp only [locSize, Nat.sub_zero, Nat.add_sub_cancel, List.range'_succ, List.range'_zero]
    simp only [locations, withOutside] at *
    simp only [Option.toArray_none, Option.toArray_some, Array.map_empty, Array.map_singleton,
      Array.empty_append, Array.append_empty, Array.append_assoc] at *
    simp [readLocation, readStatus, UniValMap.get,
      UniIndex.toNat, Permission.associatedAccess, Id.run, bind, pure]
    try simp_release_set
    try simp [outer_exposure_release, distinct]

theorem outer_initial_release (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : StageMask tags protections 4 false)
    (capacity offset finish : UInt64) (distinct : Function.Injective tags) :
    let locations := partitionWithInside capacity offset finish rootLocation (location4 true)
    (tree4 tags locations).releaseProtector (tags 1) protections =
      ⟨tree4 tags locations, .Released⟩ := by
  have release := outer_release_single tags protections mask
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, RangeMapNonempty.homogeneous, withOutside]

open Lean Elab Command in
run_cmd do
  for declaration in [``outer_access_local, ``outer_initial_release] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved four-node root release {dependency}"
end DuplicatePrefix.FourNodeRelease
