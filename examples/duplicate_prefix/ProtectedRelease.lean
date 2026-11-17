import duplicate_prefix.ProtectedBorrowAccess
import duplicate_prefix.NestedRelease

namespace DuplicatePrefix.ProtectedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess BorrowRelease NestedBorrowAccess NestedRelease ProtectedBorrowAccess MixedRelease
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

theorem outer_normal_protected (written : Bool) :
    (nestedNormalWithHelper written false).performAccess 1 (releaseKind written) .SkipChildrenOfAccessed =
      ⟨nestedNormal written, 0, [⟨1, .LocalAccess⟩, ⟨0, .LocalAccess⟩], .Completed⟩ := by
  cases written <;> decide

abbrev outerAccess (tags : Fin 6 → BorTag) (locations : DedupRangeMap LocationTree) (protections : ProtectedTags)
    (written : Bool) (range : ByteRange) :=
  source_tree_access_at (nestedTree tags locations) (nestedLocation written)
    (some ⟨1⟩) (releaseKind written) protections .SkipChildrenOfAccessed range

theorem outer_access_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (protections : ProtectedTags) (written : Bool) (range : ByteRange) (mask : SixMask tags protections false) :
    source_access_location (outerAccess tags locations protections written range) = nestedLocation written ∧
    source_access_status (outerAccess tags locations protections written range) = none := by
  have eqTags (i j : Fin 6) : tags i = tags j ↔ i = j :=
    ⟨fun h => distinct h, fun h => congrArg tags h⟩
  unfold outerAccess
  simp_tree_helpers
  simp only [BorrowTree.performNormalAccessAt, projection6 tags locations written false protections mask,
    show (⟨1⟩ : UniIndex).toNat = 1 from rfl, outer_normal_protected]
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

theorem end2_local (root child : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (range : ByteRange) (distinct : root ≠ child) (protections : ProtectedTags)
    (rootFree : protections.contains root = false) (childHeld : protections.contains child = true) :
    source_access_location (access2 root child locations written (BorrowRelease.endKind written)
      .SkipChildrenOfAccessed protections range) = childLocation written ∧
    source_access_status (access2 root child locations written (BorrowRelease.endKind written)
      .SkipChildrenOfAccessed protections range) = none := by
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  cases written
  · simpa [BorrowRelease.endKind, readNotWrite] using
      access2_local root child locations false .Read .SkipChildrenOfAccessed range distinct protections rootFree childHeld
  · simpa [BorrowRelease.endKind] using
      access2_local root child locations true .Write .SkipChildrenOfAccessed range distinct protections rootFree childHeld

theorem end6_helper_local (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (locations : DedupRangeMap LocationTree) (protections : ProtectedTags) (mask : SixMask tags protections true)
    (range : ByteRange) :
    source_access_location (access6 tags locations false .Read .SkipChildrenOfAccessed protections range) = nestedLocation false ∧
    source_access_status (access6 tags locations false .Read .SkipChildrenOfAccessed protections range) = none := by
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simpa [readNotWrite] using access6_local tags distinct locations false true protections mask .Read .SkipChildrenOfAccessed range

theorem two_release_middle (rootTag childTag : BorTag) (protections : ProtectedTags)
    (rootFree : protections.contains rootTag = false) (childHeld : protections.contains childTag = true) (before after tail : Option ByteRange)
    (source destination : ByteRange) (distinct : rootTag ≠ childTag) :
    let segments := #[⟨source, childLocation false⟩, ⟨destination, childLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, childLocation false⟩)
    let locations := withOutside before after segments
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag protections =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    (#[⟨source, childLocation false⟩, ⟨destination, childLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, childLocation false⟩))
  have readLocation (range : ByteRange) :=
    (end2_local rootTag childTag locations false range distinct protections rootFree childHeld).1
  have readStatus (range : ByteRange) :=
    (end2_local rootTag childTag locations false range distinct protections rootFree childHeld).2
  have writeLocation (range : ByteRange) :=
    (end2_local rootTag childTag locations true range distinct protections rootFree childHeld).1
  have writeStatus (range : ByteRange) :=
    (end2_local rootTag childTag locations true range distinct protections rootFree childHeld).2
  simp only [access2, BorrowRelease.endKind, Bool.false_eq_true, ↓reduceIte] at readLocation readStatus writeLocation writeStatus
  change (canonicalChildTree rootTag childTag locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [canonical_child_index rootTag childTag locations distinct]
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
    try simp [canonical_exposure_release, distinct]

theorem two_release_single (rootTag childTag : BorTag) (protections : ProtectedTags)
    (rootFree : protections.contains rootTag = false) (childHeld : protections.contains childTag = true) (before after : Option ByteRange)
    (source : ByteRange) (distinct : rootTag ≠ childTag) :
    let segments := #[⟨source, childLocation false⟩]
    let locations := withOutside before after segments
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag protections =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    #[⟨source, childLocation false⟩]
  have readLocation (range : ByteRange) :=
    (end2_local rootTag childTag locations false range distinct protections rootFree childHeld).1
  have readStatus (range : ByteRange) :=
    (end2_local rootTag childTag locations false range distinct protections rootFree childHeld).2
  simp only [access2, BorrowRelease.endKind, Bool.false_eq_true, ↓reduceIte] at readLocation readStatus
  change (canonicalChildTree rootTag childTag locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [canonical_child_index rootTag childTag locations distinct]
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
    try simp [canonical_exposure_release, distinct]

theorem two_initial_release (rootTag childTag : BorTag) (protections : ProtectedTags)
    (rootFree : protections.contains rootTag = false) (childHeld : protections.contains childTag = true)
    (capacity offset finish : UInt64) (distinct : rootTag ≠ childTag) :
    let locations := partitionWithInside capacity offset finish rootLocation (childLocation false)
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag protections =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  have release := two_release_single rootTag childTag protections rootFree childHeld
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, RangeMapNonempty.homogeneous, withOutside]

theorem two_double_release (rootTag childTag : BorTag) (protections : ProtectedTags)
    (rootFree : protections.contains rootTag = false) (childHeld : protections.contains childTag = true)
    (capacity offset finish first second : UInt64) (distinct : rootTag ≠ childTag) :
    let locations := MixedRangeMap.doubleSplit capacity offset finish first second
      rootLocation (childLocation false) (childLocation true) (childLocation false)
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag protections =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  have release := two_release_middle rootTag childTag protections rootFree childHeld
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    (if second = finish then none else some ⟨second, finish⟩)
    ⟨offset, first⟩ ⟨first, second⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    by_cases cut : second = finish <;>
    simp_all [MixedRangeMap.doubleSplit, withOutside]

theorem helper6_release_single (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections true) (before after : Option ByteRange)
    (source : ByteRange) (distinct : Function.Injective tags) :
    let segments := #[⟨source, nestedLocation false⟩]
    let locations := withOutside before after segments
    (nestedTree tags locations).releaseProtector (tags 5) (protections) =
      ⟨nestedTree tags locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    #[⟨source, nestedLocation false⟩]
  have readLocation (range : ByteRange) :=
    (end6_helper_local tags distinct locations protections mask range).1
  have readStatus (range : ByteRange) :=
    (end6_helper_local tags distinct locations protections mask range).2
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [access6, readNotWrite, Bool.false_or] at readLocation readStatus
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

theorem helper6_initial_release (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections true)
    (capacity offset finish : UInt64) (distinct : Function.Injective tags) :
    let locations := partitionWithInside capacity offset finish rootLocation (nestedLocation false)
    (nestedTree tags locations).releaseProtector (tags 5) protections =
      ⟨nestedTree tags locations, .Released⟩ := by
  have release := helper6_release_single tags protections mask
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, RangeMapNonempty.homogeneous, withOutside]

theorem outer_release_middle (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections false) (before after tail : Option ByteRange)
    (source destination : ByteRange) (distinct : Function.Injective tags) :
    let segments := #[⟨source, nestedLocation false⟩, ⟨destination, nestedLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, nestedLocation false⟩)
    let locations := withOutside before after segments
    (nestedTree tags locations).releaseProtector (tags 1) protections =
      ⟨nestedTree tags locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    (#[⟨source, nestedLocation false⟩, ⟨destination, nestedLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, nestedLocation false⟩))
  have readLocation (range : ByteRange) :=
    (outer_access_local tags distinct locations protections false range mask).1
  have readStatus (range : ByteRange) :=
    (outer_access_local tags distinct locations protections false range mask).2
  have writeLocation (range : ByteRange) :=
    (outer_access_local tags distinct locations protections true range mask).1
  have writeStatus (range : ByteRange) :=
    (outer_access_local tags distinct locations protections true range mask).2
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

theorem outer_release_single (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections false) (before after : Option ByteRange)
    (source : ByteRange) (distinct : Function.Injective tags) :
    let segments := #[⟨source, nestedLocation false⟩]
    let locations := withOutside before after segments
    (nestedTree tags locations).releaseProtector (tags 1) (protections) =
      ⟨nestedTree tags locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    #[⟨source, nestedLocation false⟩]
  have readLocation (range : ByteRange) :=
    (outer_access_local tags distinct locations protections false range mask).1
  have readStatus (range : ByteRange) :=
    (outer_access_local tags distinct locations protections false range mask).2
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

theorem outer_initial_release (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections false)
    (capacity offset finish : UInt64) (distinct : Function.Injective tags) :
    let locations := partitionWithInside capacity offset finish rootLocation (nestedLocation false)
    (nestedTree tags locations).releaseProtector (tags 1) protections =
      ⟨nestedTree tags locations, .Released⟩ := by
  have release := outer_release_single tags protections mask
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, RangeMapNonempty.homogeneous, withOutside]

theorem outer_double_release (tags : Fin 6 → BorTag) (protections : ProtectedTags) (mask : SixMask tags protections false)
    (capacity offset finish first second : UInt64) (distinct : Function.Injective tags) :
    let locations := MixedRangeMap.doubleSplit capacity offset finish first second
      rootLocation (nestedLocation false) (nestedLocation true) (nestedLocation false)
    (nestedTree tags locations).releaseProtector (tags 1) protections =
      ⟨nestedTree tags locations, .Released⟩ := by
  have release := outer_release_middle tags protections mask
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    (if second = finish then none else some ⟨second, finish⟩)
    ⟨offset, first⟩ ⟨first, second⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    by_cases cut : second = finish <;>
    simp_all [MixedRangeMap.doubleSplit, withOutside]


#print axioms two_initial_release
#print axioms two_double_release
#print axioms helper6_initial_release
#print axioms outer_initial_release
#print axioms outer_double_release
#print axioms outer_access_local
#print axioms end2_local
#print axioms end6_helper_local
end DuplicatePrefix.ProtectedRelease

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ProtectedRelease.two_initial_release,
      ``DuplicatePrefix.ProtectedRelease.two_double_release,
      ``DuplicatePrefix.ProtectedRelease.helper6_initial_release,
      ``DuplicatePrefix.ProtectedRelease.outer_initial_release,
      ``DuplicatePrefix.ProtectedRelease.outer_double_release] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
