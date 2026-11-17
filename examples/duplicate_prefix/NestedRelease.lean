import duplicate_prefix.NestedBorrowAccess
import duplicate_prefix.MixedRelease

namespace DuplicatePrefix.NestedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess NestedBorrowAccess MixedRelease
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

abbrev releaseKind (written : Bool) : AccessKind := if written then .Write else .Read

theorem outer_normal_release (written : Bool) :
    (nestedNormal written).performAccess 1 (releaseKind written) .SkipChildrenOfAccessed =
      ⟨nestedNormal written, 0, [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩], .Completed⟩ := by
  cases written <;> decide

private theorem loop_yield {β : Type} (f : Unit → β → Id (ForInStep β))
    (initial next : β) (step : f () initial = .yield next) :
    Lean.Loop.forIn {} initial f = Lean.Loop.forIn {} next f := by
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [step, bind, pure]

theorem outer_min_exposed (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) :
    source_min_exposed (nestedTree tags locations) ⟨1⟩ = none := by
  unfold_min_exposed
  simp only [Id.run, bind, pure, ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have step0 : scan () (none, #[⟨1⟩], 0, none) = .yield (none, #[⟨2⟩, ⟨4⟩], 1, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure, ← Array.forIn_toList]
  have step1 : scan () (none, #[⟨2⟩, ⟨4⟩], 1, none) = .yield (none, #[⟨2⟩, ⟨5⟩], 2, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure, ← Array.forIn_toList]
  have step2 : scan () (none, #[⟨2⟩, ⟨5⟩], 2, none) = .yield (none, #[⟨2⟩], 3, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure, ← Array.forIn_toList]
  have step3 : scan () (none, #[⟨2⟩], 3, none) = .yield (none, #[⟨3⟩], 4, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure, ← Array.forIn_toList]
  have step4 : scan () (none, #[⟨3⟩], 4, none) = .yield (none, #[], 5, none) := by
    simp [scan, UniValMap.size, UniValMap.get, UniIndex.toNat, bind, pure, ← Array.forIn_toList]
  have last : scan () (none, #[], 5, none) = .done (none, #[], 5, none) := by
    simp [scan, UniValMap.size, bind, pure]
  rw [loop_yield scan _ _ step0, loop_yield scan _ _ step1, loop_yield scan _ _ step2,
    loop_yield scan _ _ step3]
  have final := RangeMapNonempty.loop_one_update scan _ _ step4 last
  simp [final, bind, pure]

abbrev outerAccess (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (range : ByteRange) :=
  source_tree_access_at (nestedTree tags locations) (nestedLocation written)
    (some ⟨1⟩) (releaseKind written) (nestedProtected tags) .SkipChildrenOfAccessed range

theorem outer_access_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (written : Bool) (range : ByteRange) :
    source_access_location (outerAccess tags locations written range) = nestedLocation written ∧
    source_access_status (outerAccess tags locations written range) = none := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  unfold outerAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, nested_projection tags distinct locations written,
    show (⟨1⟩ : UniIndex).toNat = 1 from rfl, outer_normal_release]
  simp [nestedTree, nestedLocation, nestedNormal, nestedProtected, childProtected,
    BorrowTree.nodeAt, UniValMap.get, UniValMap.entries,
    UniIndex.ofNat?, UniIndex.toNat, TreeNode.defaultLocationState,
    ProtectedTags.contains, ProtectedTags.get, Array.find?_singleton, eqTags, outer_min_exposed,
    bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]
  simp_tree_helpers
  simp [outer_min_exposed, Id.run, UniIndex.toNat, UniValMap.get, UniValMap.insert, UniValMap.extendTo,
    BorrowTree.nodeAt, bind, pure, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.range'_succ, List.range'_zero]

theorem outer_index (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) :
    (nestedTree tags locations).indexOfTag (tags 1) = some ⟨1⟩ := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  simp only [BorrowTree.indexOfTag, nestedTree, UniKeyMap.get]
  rw [← Array.find?_toList]
  simp [eqTags]

theorem outer_exposure_release (tags : Fin 6 → BorTag)
    (locations : DedupRangeMap LocationTree) (distinct : Function.Injective tags) :
    (nestedTree tags locations).updateExposureForProtectorRelease (tags 1) =
      ⟨nestedTree tags locations, .ok ()⟩ := by
  unfold BorrowTree.updateExposureForProtectorRelease
  dsimp only
  rw [outer_index tags distinct locations]
  simp [BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, pure]

theorem helper_exposure_release (tags : Fin 6 → BorTag)
    (locations : DedupRangeMap LocationTree) (distinct : Function.Injective tags) :
    (nestedTree tags locations).updateExposureForProtectorRelease (tags 5) =
      ⟨nestedTree tags locations, .ok ()⟩ := by
  unfold BorrowTree.updateExposureForProtectorRelease
  dsimp only
  rw [nested_index tags distinct locations]
  simp [BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, pure]

theorem release_single (tags : Fin 6 → BorTag) (before after : Option ByteRange)
    (source : ByteRange) (distinct : Function.Injective tags) :
    let segments := #[⟨source, nestedLocation false⟩]
    let locations := withOutside before after segments
    (nestedTree tags locations).releaseProtector (tags 5) ((nestedProtectedWithHelper tags true)) =
      ⟨nestedTree tags locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    #[⟨source, nestedLocation false⟩]
  have readLocation (range : ByteRange) :=
    (nested_access_local_with_helper tags distinct locations false true .Read .SkipChildrenOfAccessed range).1
  have readStatus (range : ByteRange) :=
    (nested_access_local_with_helper tags distinct locations false true .Read .SkipChildrenOfAccessed range).2
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [nestedAccessWithHelper, readNotWrite, Bool.false_or] at readLocation readStatus
  change (nestedTree tags locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [nested_index tags distinct locations]
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
    try simp [helper_exposure_release, distinct]

theorem helper_initial_release (tags : Fin 6 → BorTag)
    (capacity offset finish : UInt64) (distinct : Function.Injective tags) :
    let locations := partitionWithInside capacity offset finish rootLocation (nestedLocation false)
    (nestedTree tags locations).releaseProtector (tags 5) (nestedProtectedWithHelper tags true) =
      ⟨nestedTree tags locations, .Released⟩ := by
  have release := release_single tags
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, RangeMapNonempty.homogeneous, withOutside]

theorem outer_release_middle (tags : Fin 6 → BorTag) (before after tail : Option ByteRange)
    (source destination : ByteRange) (distinct : Function.Injective tags) :
    let segments := #[⟨source, nestedLocation false⟩, ⟨destination, nestedLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, nestedLocation false⟩)
    let locations := withOutside before after segments
    (nestedTree tags locations).releaseProtector (tags 1) (nestedProtected tags) =
      ⟨nestedTree tags locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    (#[⟨source, nestedLocation false⟩, ⟨destination, nestedLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, nestedLocation false⟩))
  have readLocation (range : ByteRange) :=
    (outer_access_local tags distinct locations false range).1
  have readStatus (range : ByteRange) :=
    (outer_access_local tags distinct locations false range).2
  have writeLocation (range : ByteRange) :=
    (outer_access_local tags distinct locations true range).1
  have writeStatus (range : ByteRange) :=
    (outer_access_local tags distinct locations true range).2
  simp only [outerAccess, releaseKind, Bool.false_eq_true, ↓reduceIte] at readLocation readStatus writeLocation writeStatus
  change (nestedTree tags locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [outer_index tags distinct locations]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  cases before <;> cases after <;> cases tail
  all_goals
    first
    | have locSize : locations.entries.size = 2 := by simp [locations, withOutside]
    | have locSize : locations.entries.size = 3 := by simp [locations, withOutside]
    | have locSize : locations.entries.size = 4 := by simp [locations, withOutside]
    | have locSize : locations.entries.size = 5 := by simp [locations, withOutside]
    simp only [locSize, Nat.sub_zero, Nat.add_sub_cancel, List.range'_succ, List.range'_zero]
    simp only [locations, withOutside] at *
    simp only [Option.toArray_none, Option.toArray_some, Array.map_empty, Array.map_singleton,
      Array.empty_append, Array.append_empty, Array.append_assoc] at *
    simp [readLocation, readStatus, writeLocation, writeStatus, UniValMap.get,
      UniIndex.toNat, Permission.associatedAccess, Id.run, bind, pure]
    try simp_release_set
    try simp [outer_exposure_release, distinct]

theorem outer_release_single (tags : Fin 6 → BorTag) (before after : Option ByteRange)
    (source : ByteRange) (distinct : Function.Injective tags) :
    let segments := #[⟨source, nestedLocation false⟩]
    let locations := withOutside before after segments
    (nestedTree tags locations).releaseProtector (tags 1) ((nestedProtected tags)) =
      ⟨nestedTree tags locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    #[⟨source, nestedLocation false⟩]
  have readLocation (range : ByteRange) :=
    (outer_access_local tags distinct locations false range).1
  have readStatus (range : ByteRange) :=
    (outer_access_local tags distinct locations false range).2
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [outerAccess, releaseKind, Bool.false_eq_true, ↓reduceIte] at readLocation readStatus
  change (nestedTree tags locations).releaseProtector _ _ = _
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

theorem outer_initial_release (tags : Fin 6 → BorTag)
    (capacity offset finish : UInt64) (distinct : Function.Injective tags) :
    let locations := partitionWithInside capacity offset finish rootLocation (nestedLocation false)
    (nestedTree tags locations).releaseProtector (tags 1) (nestedProtected tags) =
      ⟨nestedTree tags locations, .Released⟩ := by
  have release := outer_release_single tags
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, RangeMapNonempty.homogeneous, withOutside]

theorem outer_double_release (tags : Fin 6 → BorTag)
    (capacity offset finish first second : UInt64) (distinct : Function.Injective tags) :
    let locations := MixedRangeMap.doubleSplit capacity offset finish first second
      rootLocation (nestedLocation false) (nestedLocation true) (nestedLocation false)
    (nestedTree tags locations).releaseProtector (tags 1) (nestedProtected tags) =
      ⟨nestedTree tags locations, .Released⟩ := by
  have release := outer_release_middle tags
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    (if second = finish then none else some ⟨second, finish⟩)
    ⟨offset, first⟩ ⟨first, second⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    by_cases cut : second = finish <;>
    simp_all [MixedRangeMap.doubleSplit, withOutside]

#print axioms outer_initial_release
#print axioms outer_double_release
#print axioms helper_initial_release
end DuplicatePrefix.NestedRelease

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.NestedRelease.helper_initial_release,
      ``DuplicatePrefix.NestedRelease.outer_initial_release, ``DuplicatePrefix.NestedRelease.outer_double_release] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "helper_initial_release depends on unapproved axiom {dependency}"
