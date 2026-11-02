import Lean
import duplicate_prefix.BorrowRangeAccess

/-! Actual read-prefix then disjoint-write Tree Borrows range transitions. -/
namespace DuplicatePrefix.BorrowCopyRanges
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open DuplicatePrefix.BorrowRangeAccess
open Lean Elab Tactic

def copyPartition {α : Type} (capacity boundary finish : UInt64) (left middle right : α) : DedupRangeMap α :=
  if finish = capacity then ⟨#[⟨⟨0, boundary⟩, left⟩, ⟨⟨boundary, capacity⟩, middle⟩]⟩
  else ⟨#[⟨⟨0, boundary⟩, left⟩, ⟨⟨boundary, finish⟩, middle⟩,
    ⟨⟨finish, capacity⟩, right⟩]⟩

elab "simp_copy_set" : tactic => do
  let env ← getEnv
  let names ← [".DedupRangeMap.segmentAt?", ".DedupRangeMap.updateAt"].mapM fun (suffix : String) => do
    let candidates := env.constants.toList.filterMap fun (name, _) =>
      if name.toString.endsWith suffix then some name else none
    match candidates with
    | [name] => pure (mkIdent name)
    | _ => throwError "expected helper {suffix}, found {candidates.length}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all [DedupRangeMap.setAtPos,
    RangeMapNonempty.dividedWindow, RangeMapNonempty.divided, copyPartition,
    Id.run, bind, pure, Except.bind, Except.pure, $[$names:ident],*]))

theorem divided_window_set_middle {α : Type} (capacity boundary finish : UInt64)
    (left right replacement : α) :
    (RangeMapNonempty.dividedWindow capacity boundary finish left right).setAtPos 1 replacement =
      ⟨copyPartition capacity boundary finish left replacement right, .ok ()⟩ := by
  by_cases stop : finish = capacity <;> simp_copy_set

theorem child_divided_range_access (rootTag childTag : BorTag)
    (capacity boundary len : UInt64) (leftWritten rightWritten : Bool) (kind : AccessKind)
    (distinct : rootTag ≠ childTag) (positiveLength : (0 : UInt64) < len)
    (bounds : boundary.toNat + len.toNat ≤ capacity.toNat) :
    ((canonicalChildTree rootTag childTag
      (RangeMapNonempty.divided capacity boundary (childLocation leftWritten) (childLocation rightWritten))).performBorrowAccessRange (.concrete childTag) (Size.ofBytes boundary) (Size.ofBytes len)
        kind (childProtected childTag) .VisitChildrenOfAccessed).status = .Completed := by
  have accessFact := child_access_local rootTag childTag
    (RangeMapNonempty.divided capacity boundary (childLocation leftWritten) (childLocation rightWritten))
    rightWritten kind ⟨boundary, boundary + len⟩ distinct
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [canonical_child_index rootTag childTag _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [RangeMapNonempty.iter_mut_divided_boundary capacity boundary len
    (childLocation leftWritten) (childLocation rightWritten) positiveLength bounds]
  simp [accessFact.1, accessFact.2, divided_window_set_middle, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem child_divided_range_tree (rootTag childTag : BorTag)
    (capacity boundary len : UInt64) (leftWritten rightWritten : Bool) (kind : AccessKind)
    (distinct : rootTag ≠ childTag) (positiveLength : (0 : UInt64) < len)
    (bounds : boundary.toNat + len.toNat ≤ capacity.toNat) :
    ((canonicalChildTree rootTag childTag
      (RangeMapNonempty.divided capacity boundary (childLocation leftWritten) (childLocation rightWritten))).performBorrowAccessRange (.concrete childTag) (Size.ofBytes boundary) (Size.ofBytes len)
        kind (childProtected childTag) .VisitChildrenOfAccessed).tree =
      canonicalChildTree rootTag childTag
        (copyPartition capacity boundary (boundary + len) (childLocation leftWritten)
          (childLocation (rightWritten || kind == .Write)) (childLocation rightWritten)) := by
  have accessFact := child_access_local rootTag childTag
    (RangeMapNonempty.divided capacity boundary (childLocation leftWritten) (childLocation rightWritten))
    rightWritten kind ⟨boundary, boundary + len⟩ distinct
  unfold BorrowTree.performBorrowAccessRange
  dsimp only
  rw [canonical_child_index rootTag childTag _ distinct]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
  rw [RangeMapNonempty.iter_mut_divided_boundary capacity boundary len
    (childLocation leftWritten) (childLocation rightWritten) positiveLength bounds]
  simp [accessFact.1, accessFact.2, divided_window_set_middle, Id.run, bind, pure,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]

theorem canonical_copy_borrow_access (rootTag childTag : BorTag) (capacity n : UInt64)
    (distinct : rootTag ≠ childTag) (positive : (0 : UInt64) < n)
    (bounds : n.toNat + n.toNat ≤ capacity.toNat) :
    let initial := canonicalChildTree rootTag childTag
      (DedupRangeMap.new (Size.ofBytes capacity) (childLocation false))
    let read := initial.performBorrowAccessRange (.concrete childTag) Size.ZERO (Size.ofBytes n)
      .Read (childProtected childTag) .VisitChildrenOfAccessed
    read.status = .Completed ∧
      (read.tree.performBorrowAccessRange (.concrete childTag) (Size.ofBytes n) (Size.ofBytes n)
        .Write (childProtected childTag) .VisitChildrenOfAccessed).status = .Completed := by
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  have sourceBounds : (0 : UInt64).toNat + n.toNat ≤ capacity.toNat := by
    simp only [UInt64.toNat_zero]
    omega
  have nLess : n < capacity := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have endNe : n ≠ capacity := by
    intro equality
    subst n
    exact (UInt64.lt_irrefl capacity) nLess
  have readStatus := child_nonempty_range_access rootTag childTag capacity 0 n false .Read
    distinct positive sourceBounds
  have readTree := child_nonempty_range_tree rootTag childTag capacity 0 n false .Read
    distinct positive sourceBounds
  have writeStatus := child_divided_range_access rootTag childTag capacity n n false false .Write
    distinct positive bounds
  dsimp only
  constructor
  · exact readStatus
  · simp only [Size.ZERO, Size.ofBytes] at readTree ⊢
    rw [readTree]
    simpa [partitionWithInside, RangeMapNonempty.divided, endNe, Size.ofBytes, readNotWrite] using writeStatus

theorem canonical_copy_borrow_tree (rootTag childTag : BorTag) (capacity n : UInt64)
    (distinct : rootTag ≠ childTag) (positive : (0 : UInt64) < n)
    (bounds : n.toNat + n.toNat ≤ capacity.toNat) :
    let initial := canonicalChildTree rootTag childTag
      (DedupRangeMap.new (Size.ofBytes capacity) (childLocation false))
    let read := initial.performBorrowAccessRange (.concrete childTag) Size.ZERO (Size.ofBytes n)
      .Read (childProtected childTag) .VisitChildrenOfAccessed
    let write := read.tree.performBorrowAccessRange (.concrete childTag) (Size.ofBytes n) (Size.ofBytes n)
      .Write (childProtected childTag) .VisitChildrenOfAccessed
    write.tree = canonicalChildTree rootTag childTag
      (copyPartition capacity n (n + n) (childLocation false) (childLocation true) (childLocation false)) := by
  have readNotWrite : (AccessKind.Read == AccessKind.Write) = false := by decide
  have sourceBounds : (0 : UInt64).toNat + n.toNat ≤ capacity.toNat := by
    simp only [UInt64.toNat_zero]
    omega
  have nLess : n < capacity := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have endNe : n ≠ capacity := by
    intro equality
    subst n
    exact (UInt64.lt_irrefl capacity) nLess
  have readTree := child_nonempty_range_tree rootTag childTag capacity 0 n false .Read
    distinct positive sourceBounds
  have writeTree := child_divided_range_tree rootTag childTag capacity n n false false .Write
    distinct positive bounds
  dsimp only
  simp only [Size.ZERO, Size.ofBytes] at readTree ⊢
  rw [readTree]
  simpa [partitionWithInside, RangeMapNonempty.divided, endNe, Size.ofBytes, readNotWrite] using writeTree

#print axioms canonical_copy_borrow_access
#print axioms child_divided_range_tree
#print axioms canonical_copy_borrow_tree
end DuplicatePrefix.BorrowCopyRanges
