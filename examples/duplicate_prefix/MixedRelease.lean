import duplicate_prefix.MixedBorrowAccess
import duplicate_prefix.BorrowRelease

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace DuplicatePrefix.MixedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess BorrowRelease
open Lean Elab Tactic

def withOutside (before after : Option ByteRange) (segments : Array (RangeMapSegment LocationTree)) :
    DedupRangeMap LocationTree :=
  ⟨(before.toArray.map fun range => ⟨range, rootLocation⟩) ++ segments ++
    (after.toArray.map fun range => ⟨range, rootLocation⟩)⟩

elab "simp_release_set" : tactic => do
  let env ← getEnv
  let names ← [".DedupRangeMap.segmentAt?", ".DedupRangeMap.updateAt"].mapM fun (suffix : String) => do
    let candidates := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    match candidates with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected helper {suffix}, found {candidates.length}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all [DedupRangeMap.index, DedupRangeMap.setAtPos,
    UniValMap.get, UniIndex.toNat, Permission.associatedAccess, canonical_exposure_release,
    Id.run, bind, pure, Except.bind, Except.pure, $[$names:ident],*]))

/-- Source protector release on the copied slice, retaining optional allocation
intervals on either side. The outer intervals have no child permission. -/
theorem release_middle (rootTag childTag : BorTag) (before after tail : Option ByteRange)
    (source destination : ByteRange) (distinct : rootTag ≠ childTag) :
    let segments := #[⟨source, childLocation false⟩, ⟨destination, childLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, childLocation false⟩)
    let locations := withOutside before after segments
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag (childProtected childTag) =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    (#[⟨source, childLocation false⟩, ⟨destination, childLocation true⟩] ++
      (tail.toArray.map fun range => ⟨range, childLocation false⟩))
  have readLocation (range : ByteRange) :=
    (child_end_access_local rootTag childTag locations false range distinct).1
  have readStatus (range : ByteRange) :=
    (child_end_access_local rootTag childTag locations false range distinct).2
  have writeLocation (range : ByteRange) :=
    (child_end_access_local rootTag childTag locations true range distinct).1
  have writeStatus (range : ByteRange) :=
    (child_end_access_local rootTag childTag locations true range distinct).2
  simp only [childAccessMode, endKind, Bool.false_eq_true, ↓reduceIte] at readLocation readStatus writeLocation writeStatus
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

theorem release_single (rootTag childTag : BorTag) (before after : Option ByteRange)
    (source : ByteRange) (distinct : rootTag ≠ childTag) :
    let segments := #[⟨source, childLocation false⟩]
    let locations := withOutside before after segments
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag (childProtected childTag) =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  dsimp only
  let locations := withOutside before after
    #[⟨source, childLocation false⟩]
  have readLocation (range : ByteRange) :=
    (child_end_access_local rootTag childTag locations false range distinct).1
  have readStatus (range : ByteRange) :=
    (child_end_access_local rootTag childTag locations false range distinct).2
  simp only [childAccessMode, endKind, Bool.false_eq_true, ↓reduceIte] at readLocation readStatus
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

theorem initial_release (rootTag childTag : BorTag)
    (capacity offset finish : UInt64) (distinct : rootTag ≠ childTag) :
    let locations := partitionWithInside capacity offset finish rootLocation (childLocation false)
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag (childProtected childTag) =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  have release := release_single rootTag childTag
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    ⟨offset, finish⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_all [partitionWithInside, RangeMapNonempty.homogeneous, withOutside]

#print axioms initial_release
theorem double_release (rootTag childTag : BorTag)
    (capacity offset finish first second : UInt64) (distinct : rootTag ≠ childTag) :
    let locations := MixedRangeMap.doubleSplit capacity offset finish first second
      rootLocation (childLocation false) (childLocation true) (childLocation false)
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag (childProtected childTag) =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  have release := release_middle rootTag childTag
    (if offset = 0 then none else some ⟨0, offset⟩)
    (if finish = capacity then none else some ⟨finish, capacity⟩)
    (if second = finish then none else some ⟨second, finish⟩)
    ⟨offset, first⟩ ⟨first, second⟩ distinct
  dsimp only at release ⊢
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    by_cases cut : second = finish <;>
    simp_all [MixedRangeMap.doubleSplit, withOutside]

#print axioms release_middle
#print axioms double_release
end DuplicatePrefix.MixedRelease

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.MixedRelease.release_middle,
      ``DuplicatePrefix.MixedRelease.initial_release,
      ``DuplicatePrefix.MixedRelease.double_release] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
