import duplicate_prefix.MixedRangeMap

/-! Actual source-read and disjoint destination-write inside a retagged slice,
including unchanged parent-only allocation bytes outside that slice. -/
namespace DuplicatePrefix.MixedBorrowAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open BorrowRangeAccess MixedRangeMap

 theorem read_prefix (rootTag childTag : BorTag) (capacity offset len finish : UInt64)
    (distinct : rootTag ≠ childTag) (positive : (0 : UInt64) < len)
    (interior : offset.toNat + len.toNat < finish.toNat) :
    let initial := canonicalChildTree rootTag childTag
      (partitionWithInside capacity offset finish rootLocation (childLocation false))
    let result := initial.performBorrowAccessRange (.concrete childTag)
      (Size.ofBytes offset) (Size.ofBytes len) .Read (childProtected childTag) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree rootTag childTag
      (splitInside capacity offset finish (offset + len) rootLocation (childLocation false)) := by
  have accessFact := child_access_local rootTag childTag
    (partitionWithInside capacity offset finish rootLocation (childLocation false))
    false .Read ⟨offset, offset + len⟩ distinct
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  simp only [readNotWrite, Bool.false_or] at accessFact
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [canonical_child_index rootTag childTag _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [iterMut_initial_prefix capacity offset len finish rootLocation (childLocation false) positive interior]
  simp [accessFact.1, accessFact.2, split_set_same, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem write_prefix (rootTag childTag : BorTag) (capacity offset finish first len : UInt64)
    (distinct : rootTag ≠ childTag) (positive : (0 : UInt64) < len)
    (afterStart : offset < first) (bounds : first.toNat + len.toNat ≤ finish.toNat) :
    let initial := canonicalChildTree rootTag childTag
      (splitInside capacity offset finish first rootLocation (childLocation false))
    let result := initial.performBorrowAccessRange (.concrete childTag)
      (Size.ofBytes first) (Size.ofBytes len) .Write (childProtected childTag) .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree = canonicalChildTree rootTag childTag
      (doubleSplit capacity offset finish first (first + len) rootLocation
        (childLocation false) (childLocation true) (childLocation false)) := by
  have accessFact := child_access_local rootTag childTag
    (splitInside capacity offset finish first rootLocation (childLocation false))
    false .Write ⟨first, first + len⟩ distinct
  dsimp only
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [canonical_child_index rootTag childTag _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [iterMut_second_prefix capacity offset finish first len rootLocation (childLocation false)
    positive afterStart bounds]
  simp [accessFact.1, accessFact.2, double_set_middle, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem canonical_slice_copy_borrow (rootTag childTag : BorTag)
    (capacity offset sliceLen n : UInt64) (distinct : rootTag ≠ childTag)
    (positive : (0 : UInt64) < n)
    (sliceBounds : offset.toNat + sliceLen.toNat ≤ capacity.toNat)
    (copyBounds : n.toNat + n.toNat ≤ sliceLen.toNat) :
    let initial := canonicalChildTree rootTag childTag
      (partitionWithInside capacity offset (offset + sliceLen) rootLocation (childLocation false))
    let read := initial.performBorrowAccessRange (.concrete childTag)
      (Size.ofBytes offset) (Size.ofBytes n) .Read (childProtected childTag) .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete childTag)
      (Size.ofBytes (offset + n)) (Size.ofBytes n) .Write (childProtected childTag) .VisitChildrenOfAccessed
    read.status = .Completed ∧ write.status = .Completed ∧
      write.tree = canonicalChildTree rootTag childTag
        (doubleSplit capacity offset (offset + sliceLen) (offset + n) ((offset + n) + n)
          rootLocation (childLocation false) (childLocation true) (childLocation false)) := by
  have fits : offset.toNat + sliceLen.toNat < 2^64 := by have limit := capacity.toNat_lt; omega
  have endNat : (offset + sliceLen).toNat = offset.toNat + sliceLen.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have prefixFits : offset.toNat + n.toNat < 2^64 := by omega
  have middleNat : (offset + n).toNat = offset.toNat + n.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt prefixFits]
  have posNat : 0 < n.toNat := by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
  have prefixInterior : offset.toNat + n.toNat < (offset + sliceLen).toNat := by omega
  have afterStart : offset < offset + n := by simp only [UInt64.lt_iff_toNat_lt, middleNat]; omega
  have suffixBounds : (offset + n).toNat + n.toNat ≤ (offset + sliceLen).toNat := by omega
  have readFact := read_prefix rootTag childTag capacity offset n (offset + sliceLen)
    distinct positive prefixInterior
  have writeFact := write_prefix rootTag childTag capacity offset (offset + sliceLen) (offset + n) n
    distinct positive afterStart suffixBounds
  dsimp only at readFact writeFact ⊢
  exact ⟨readFact.1, by rw [readFact.2]; exact writeFact.1, by rw [readFact.2]; exact writeFact.2⟩

#print axioms canonical_slice_copy_borrow
#print axioms read_prefix
#print axioms write_prefix
end DuplicatePrefix.MixedBorrowAccess

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.MixedBorrowAccess.canonical_slice_copy_borrow,
      ``DuplicatePrefix.MixedBorrowAccess.read_prefix, ``DuplicatePrefix.MixedBorrowAccess.write_prefix] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
