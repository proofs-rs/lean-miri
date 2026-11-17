import duplicate_prefix.ChildBorrow
import duplicate_prefix.BorrowRangeAccess
import Init.Internal.Order.While
import Init.Data.Range.Lemmas

/-! Actual protected mutable-child insertion into an allocation root tree. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace DuplicatePrefix.ChildConstructor
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows
open Lean Elab Tactic

private def sourceName (suffix : String) : CoreM Name := do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match found with
  | [name] => pure name
  | _ => throwError "expected exact source helper {suffix}"

elab "source_sifa_update" : term => do
  return mkConst (← sourceName ".BorrowTree.updateSifaAfterRetag")

elab "unfold_sifa" : tactic => do
  let name := mkIdent (← sourceName ".BorrowTree.updateSifaAfterRetag")
  evalTactic (← `(tactic| unfold $name:ident))

elab "simp_new_source" : tactic => do
  let root := mkIdent (← sourceName ".BorrowTree.rootIndex")
  let weaker := mkIdent (← sourceName ".BorrowTree.weakerSifa")
  evalTactic (← `(tactic| simp_all (config := { maxSteps := 200000 })
    [BorrowTree.new, ChildBorrow.rootTag, ChildBorrow.childTag, ChildBorrow.rootMap,
      ChildBorrow.fnEntryLocation, BorrowRangeAccess.rootLocation,
      UniKeyMap.get, UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniIndex.toNat,
      Permission.isInitial, Permission.isUnique, Permission.newDisabled, Permission.newUnique,
      Permission.strongestIdempotentForeignAccess, DedupRangeMap.new, DedupRangeMap.iterAll,
      Size.ofBytes, Size.add, Id.run, bind, pure, Except.bind, Except.pure,
      $root:ident, $weaker:ident]))

private theorem root_sifa_unchanged (capacity offset finish : UInt64)
    (root child : BorTag) :
    let tree := BorrowRangeAccess.canonicalChildTree root child
      (BorrowRangeAccess.partitionWithInside capacity offset finish
        BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false))
    source_sifa_update tree ⟨0⟩ .None = (tree, .ok ()) := by
  let tree := BorrowRangeAccess.canonicalChildTree root child
    (BorrowRangeAccess.partitionWithInside capacity offset finish
      BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false))
  change source_sifa_update tree ⟨0⟩ .None = (tree, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, tree, some (⟨0⟩ : UniIndex), 0, true) =
      .yield (none, tree, some (⟨0⟩ : UniIndex), 0, false) := by
    by_cases atStart : offset = 0 <;> by_cases atEnd : finish = capacity <;>
      simp [scan, tree, BorrowRangeAccess.canonicalChildTree,
        BorrowRangeAccess.partitionWithInside, BorrowRangeAccess.rootLocation,
        BorrowRangeAccess.childLocation, RangeMapNonempty.homogeneous, atStart, atEnd,
        UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniValMap.size, UniIndex.toNat,
        DedupRangeMap.iterAll, DedupRangeMap.modifyAll,
        IdempotentForeignAccess.ensureNoStrongerThan, IdempotentForeignAccess.rank,
        Id.run, bind, pure]
  have last : scan () (none, tree, some (⟨0⟩ : UniIndex), 0, false) =
      .done (none, tree, some (⟨0⟩ : UniIndex), 0, false) := by
    simp [scan, bind, pure]
  have doneScan := RangeMapNonempty.loop_one_update scan _ _ first last
  simp only [doneScan, Id.run, bind, pure]

private theorem insert_fresh_mapping (root child : BorTag) (distinct : root ≠ child) :
    (⟨#[(root, ⟨0⟩)], #[]⟩ : UniKeyMap BorTag).insert child =
      .Inserted ⟨#[(root, ⟨0⟩), (child, ⟨1⟩)], #[]⟩ ⟨1⟩ := by
  simp [UniKeyMap.insert, UniKeyMap.get, UniIndex.ofNat?, distinct]

open ChildBorrow in
theorem new_child_exact (root child : BorTag) (distinct : root ≠ child)
    (capacity offset len : UInt64)
    (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    let result := (BorrowTree.new root (Size.ofBytes capacity)).newChild
      (Size.ofBytes offset) (.concrete root) child
      (DedupRangeMap.new (Size.ofBytes len) fnEntryLocation) (.ReservedFrz false) true
    result = ⟨BorrowRangeAccess.canonicalChildTree root child
        (BorrowRangeAccess.partitionWithInside capacity offset (offset + len)
          BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)), .ok ()⟩ := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have capacityPositive : capacity ≠ 0 := by
    intro h
    subst capacity
    have : len.toNat = 0 := by simp only [UInt64.toNat_zero] at bounds; omega
    exact nonzero (UInt64.toNat_inj.mp (by simpa using this))
  have locationUpdate := BorrowRangeAccess.modifyRange_new capacity offset len
    BorrowRangeAccess.rootLocation
    (fun _ location => { location with perms := location.perms.insert ⟨1⟩ fnEntryLocation })
    positive bounds
  have updateValue :
      { BorrowRangeAccess.rootLocation with perms :=
        BorrowRangeAccess.rootLocation.perms.insert ⟨1⟩ fnEntryLocation } =
      BorrowRangeAccess.childLocation false := by rfl
  rw [updateValue] at locationUpdate
  unfold BorrowTree.newChild
  have inserted : (BorrowTree.new root (Size.ofBytes capacity)).tagMapping.insert child =
      .Inserted ⟨#[(root, ⟨0⟩), (child, ⟨1⟩)], #[]⟩ ⟨1⟩ :=
    insert_fresh_mapping root child distinct
  rw [inserted]
  simp only [← Array.forIn_toList]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp_new_source
  have final := root_sifa_unchanged capacity offset (offset + len)
    root child
  exact ⟨congrArg Prod.fst final, congrArg Prod.snd final⟩

#print axioms new_child_exact

/- The parent read made by retagging has already split the location map at
the reborrow boundaries. This bridge retains those actual stored segments. -/
theorem new_child_partition_exact (root child : BorTag) (distinct : root ≠ child)
    (capacity offset len : UInt64) (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    ({BorrowTree.new root (Size.ofBytes capacity) with
      locations := RangeMapNonempty.intervalPartition capacity offset (offset + len)
        BorrowRangeAccess.rootLocation}).newChild
      (Size.ofBytes offset) (.concrete root) child
      (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation)
      (.ReservedFrz false) true =
      ⟨BorrowRangeAccess.canonicalChildTree root child
        (BorrowRangeAccess.partitionWithInside capacity offset (offset + len)
          BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false)), .ok ()⟩ := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have locationUpdate := BorrowRangeAccess.modifyRange_intervalPartition capacity offset len
    BorrowRangeAccess.rootLocation
    (fun _ location => {location with perms := location.perms.insert ⟨1⟩ ChildBorrow.fnEntryLocation})
    positive bounds
  have updateValue :
      {BorrowRangeAccess.rootLocation with perms :=
        BorrowRangeAccess.rootLocation.perms.insert ⟨1⟩ ChildBorrow.fnEntryLocation} =
      BorrowRangeAccess.childLocation false := by rfl
  rw [updateValue] at locationUpdate
  unfold BorrowTree.newChild
  have inserted : (BorrowTree.new root (Size.ofBytes capacity)).tagMapping.insert child =
      .Inserted ⟨#[(root, ⟨0⟩), (child, ⟨1⟩)], #[]⟩ ⟨1⟩ :=
    insert_fresh_mapping root child distinct
  simp only [inserted, ← Array.forIn_toList]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp_new_source
  have final := root_sifa_unchanged capacity offset (offset + len) root child
  exact ⟨congrArg Prod.fst final, congrArg Prod.snd final⟩

#print axioms new_child_partition_exact

private theorem root_sifa_unchanged_zero (capacity : UInt64) (root child : BorTag) :
    let tree := BorrowRangeAccess.canonicalChildTree root child
      (DedupRangeMap.new (Size.ofBytes capacity) BorrowRangeAccess.rootLocation)
    source_sifa_update tree ⟨0⟩ .None = (tree, .ok ()) := by
  let tree := BorrowRangeAccess.canonicalChildTree root child
    (DedupRangeMap.new (Size.ofBytes capacity) BorrowRangeAccess.rootLocation)
  change source_sifa_update tree ⟨0⟩ .None = (tree, .ok ())
  unfold_sifa
  simp only [beq_iff_eq, reduceCtorEq, ↓reduceIte, ForIn.forIn]
  name_range_scan
  have first : scan () (none, tree, some (⟨0⟩ : UniIndex), 0, true) =
      .yield (none, tree, some (⟨0⟩ : UniIndex), 0, false) := by
    by_cases empty : capacity = 0 <;>
      simp [scan, tree, BorrowRangeAccess.canonicalChildTree, BorrowRangeAccess.rootLocation,
        empty, UniValMap.get, UniValMap.insert, UniValMap.extendTo, UniValMap.size,
        UniIndex.toNat, DedupRangeMap.new, DedupRangeMap.iterAll, DedupRangeMap.modifyAll,
        Size.ofBytes, IdempotentForeignAccess.ensureNoStrongerThan,
        IdempotentForeignAccess.rank, Id.run, bind, pure]
  have last : scan () (none, tree, some (⟨0⟩ : UniIndex), 0, false) =
      .done (none, tree, some (⟨0⟩ : UniIndex), 0, false) := by
    simp [scan, bind, pure]
  have doneScan := RangeMapNonempty.loop_one_update scan _ _ first last
  simp only [doneScan, Id.run, bind, pure]

theorem new_child_zero_exact (root child : BorTag) (distinct : root ≠ child)
    (capacity offset : UInt64) :
    (BorrowTree.new root (Size.ofBytes capacity)).newChild
      (Size.ofBytes offset) (.concrete root) child
      (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true =
      ⟨BorrowRangeAccess.canonicalChildTree root child
        (DedupRangeMap.new (Size.ofBytes capacity) BorrowRangeAccess.rootLocation), .ok ()⟩ := by
  unfold BorrowTree.newChild
  have inserted : (BorrowTree.new root (Size.ofBytes capacity)).tagMapping.insert child =
      .Inserted ⟨#[(root, ⟨0⟩), (child, ⟨1⟩)], #[]⟩ ⟨1⟩ :=
    insert_fresh_mapping root child distinct
  rw [inserted]
  simp only [Size.ZERO, ← Array.forIn_toList]
  simp_new_source
  have final := root_sifa_unchanged_zero capacity root child
  simpa only [DedupRangeMap.new, Size.ofBytes, beq_iff_eq] using
    (And.intro (congrArg Prod.fst final) (congrArg Prod.snd final))

#print axioms new_child_zero_exact

end DuplicatePrefix.ChildConstructor

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.ChildConstructor.new_child_exact,
      ``DuplicatePrefix.ChildConstructor.new_child_partition_exact,
      ``DuplicatePrefix.ChildConstructor.new_child_zero_exact] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
