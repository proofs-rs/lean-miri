import duplicate_prefix.BorrowCopyRanges

/-! Source protector-release facts for the canonical protected mutable child. -/
namespace DuplicatePrefix.BorrowRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open DuplicatePrefix.BorrowRangeAccess

/-- Updating a stored interval with its own payload leaves the actual range
map unchanged. The index premise is a structural lookup, not an access result. -/
theorem setAtPos_index_self {α : Type} (map : DedupRangeMap α) (position : Nat)
    (segment : RangeMapSegment α) (lookup : map.index position = .ok segment) :
    map.setAtPos position segment.data = ⟨map, .ok ()⟩ := by
  by_cases valid : position < map.entries.size
  · have same : map.entries[position] = segment := by
      unfold DedupRangeMap.index at lookup
      simp_range_updates
    subst segment
    simp_range_updates
    have eta : ({ range := map.entries[position].range, data := map.entries[position].data } :
        RangeMapSegment α) = map.entries[position] := by
      cases map.entries[position]
      rfl
    rw [eta, Array.set_getElem_self valid]
  · unfold DedupRangeMap.index at lookup
    simp_range_updates

def endKind (written : Bool) : AccessKind := if written then .Write else .Read

theorem child_end_access_local (rootTag childTag : BorTag) (locations : DedupRangeMap LocationTree)
    (written : Bool) (range : ByteRange) (distinct : rootTag ≠ childTag) :
    source_access_location
      (childAccessMode rootTag childTag locations written (endKind written) .SkipChildrenOfAccessed range) =
      childLocation written ∧
    source_access_status
      (childAccessMode rootTag childTag locations written (endKind written) .SkipChildrenOfAccessed range) = none := by
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  cases written
  · simpa [endKind, readNotWrite] using
      child_access_local_mode rootTag childTag locations false .Read .SkipChildrenOfAccessed range distinct
  · simpa [endKind] using
      child_access_local_mode rootTag childTag locations true .Write .SkipChildrenOfAccessed range distinct

theorem canonical_exposure_release (rootTag childTag : BorTag)
    (locations : DedupRangeMap LocationTree) (distinct : rootTag ≠ childTag) :
    (canonicalChildTree rootTag childTag locations).updateExposureForProtectorRelease childTag =
      ⟨canonicalChildTree rootTag childTag locations, .ok ()⟩ := by
  unfold BorrowTree.updateExposureForProtectorRelease
  dsimp only
  rw [canonical_child_index rootTag childTag locations distinct]
  simp [BorrowTree.nodeAt, UniValMap.get, UniIndex.toNat, Id.run, bind, pure]

theorem release_two (rootTag childTag : BorTag) (a b : ByteRange)
    (x y : Bool) (distinct : rootTag ≠ childTag) :
    let locations : DedupRangeMap LocationTree := ⟨#[⟨a, childLocation x⟩, ⟨b, childLocation y⟩]⟩
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag (childProtected childTag) =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  dsimp only
  let locations : DedupRangeMap LocationTree := ⟨#[⟨a, childLocation x⟩, ⟨b, childLocation y⟩]⟩
  have ix0 : locations.index 0 = .ok ⟨a, childLocation x⟩ := by rfl
  have ix1 : locations.index 1 = .ok ⟨b, childLocation y⟩ := by rfl
  have set0 := setAtPos_index_self locations 0 _ ix0
  have set1 := setAtPos_index_self locations 1 _ ix1
  have access0 := child_end_access_local rootTag childTag locations x a distinct
  have access1 := child_end_access_local rootTag childTag locations y b distinct
  change (canonicalChildTree rootTag childTag locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [canonical_child_index rootTag childTag locations distinct]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [show locations.entries.size = 2 from rfl, Nat.sub_zero, Nat.add_sub_cancel,
    List.range'_succ, List.range'_zero]
  cases x <;> cases y <;>
    simp only [childAccessMode, endKind, Bool.false_eq_true, ↓reduceIte] at access0 access1 <;>
    simp [canonical_exposure_release, distinct, ix0, ix1, set0, set1,
      access0.1, access0.2, access1.1, access1.2,
      UniValMap.get, UniIndex.toNat, Permission.associatedAccess,
      Id.run, bind, pure] <;> rfl

theorem release_three (rootTag childTag : BorTag) (a b c : ByteRange)
    (x y z : Bool) (distinct : rootTag ≠ childTag) :
    let locations : DedupRangeMap LocationTree := ⟨#[⟨a, childLocation x⟩, ⟨b, childLocation y⟩, ⟨c, childLocation z⟩]⟩
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag (childProtected childTag) =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  dsimp only
  let locations : DedupRangeMap LocationTree := ⟨#[⟨a, childLocation x⟩, ⟨b, childLocation y⟩, ⟨c, childLocation z⟩]⟩
  have ix0 : locations.index 0 = .ok ⟨a, childLocation x⟩ := by rfl
  have ix1 : locations.index 1 = .ok ⟨b, childLocation y⟩ := by rfl
  have ix2 : locations.index 2 = .ok ⟨c, childLocation z⟩ := by rfl
  have set2 := setAtPos_index_self locations 2 _ ix2
  have access2 := child_end_access_local rootTag childTag locations z c distinct
  have set0 := setAtPos_index_self locations 0 _ ix0
  have set1 := setAtPos_index_self locations 1 _ ix1
  have access0 := child_end_access_local rootTag childTag locations x a distinct
  have access1 := child_end_access_local rootTag childTag locations y b distinct
  change (canonicalChildTree rootTag childTag locations).releaseProtector _ _ = _
  unfold BorrowTree.releaseProtector
  dsimp only
  rw [canonical_child_index rootTag childTag locations distinct]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  simp only [show locations.entries.size = 3 from rfl, Nat.sub_zero, Nat.add_sub_cancel,
    List.range'_succ, List.range'_zero]
  cases x <;> cases y <;> cases z <;>
    simp only [childAccessMode, endKind, Bool.false_eq_true, ↓reduceIte] at access0 access1 access2 <;>
    simp [canonical_exposure_release, distinct, ix0, ix1, ix2, set0, set1, set2,
      access0.1, access0.2, access1.1, access1.2, access2.1, access2.2,
      UniValMap.get, UniIndex.toNat, Permission.associatedAccess,
      Id.run, bind, pure] <;> rfl

theorem canonical_copy_release (rootTag childTag : BorTag) (capacity n : UInt64)
    (distinct : rootTag ≠ childTag) :
    let locations := BorrowCopyRanges.copyPartition capacity n (n + n)
      (childLocation false) (childLocation true) (childLocation false)
    (canonicalChildTree rootTag childTag locations).releaseProtector childTag (childProtected childTag) =
      ⟨canonicalChildTree rootTag childTag locations, .Released⟩ := by
  dsimp only
  by_cases stop : n + n = capacity
  · simpa [BorrowCopyRanges.copyPartition, stop] using
      release_two rootTag childTag ⟨0, n⟩ ⟨n, capacity⟩ false true distinct
  · simpa [BorrowCopyRanges.copyPartition, stop] using
      release_three rootTag childTag ⟨0, n⟩ ⟨n, n + n⟩ ⟨n + n, capacity⟩
        false true false distinct

#print axioms canonical_copy_release
#print axioms release_two
#print axioms release_three
#print axioms setAtPos_index_self
#print axioms child_end_access_local
#print axioms canonical_exposure_release
end DuplicatePrefix.BorrowRelease

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.BorrowRelease.canonical_copy_release,
      ``DuplicatePrefix.BorrowRelease.release_two, ``DuplicatePrefix.BorrowRelease.release_three] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
