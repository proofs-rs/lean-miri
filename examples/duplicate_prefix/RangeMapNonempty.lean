import Lean
import Init.Internal.Order.While
import Miri.DataStructures.DedupRangeMap

/-! Symbolic homogeneous-map interval proofs for the actual range iterator.
The while loops are unfolded with Lean's kernel-checked MonadTail equation. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

namespace DuplicatePrefix.RangeMapNonempty
open Miri.ABI Miri.DataStructures
open Lean Elab Tactic

private def sourceHelper (suffix : String) : CoreM Name := do
  let candidates := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError "expected unique source helper {suffix}; found {candidates.length}"

elab "range_find_offset" : term => do
  return mkConst (← sourceHelper ".DedupRangeMap.findOffset")

elab "range_split_index" : term => do
  return mkConst (← sourceHelper ".DedupRangeMap.splitIndex")
elab "range_checked_end" : term => do
  return mkConst (← sourceHelper ".DedupRangeMap.checkedEnd")
elab "range_selected_slice" : term => do
  return mkConst (← sourceHelper ".DedupRangeMap.selectedSlice")
elab "range_segment_at" : term => do
  return mkConst (← sourceHelper ".DedupRangeMap.segmentAt?")

elab "simp_range_helpers" : tactic => do
  let names ← [".DedupRangeMap.findOffset", ".DedupRangeMap.segmentAt?",
    ".DedupRangeMap.splitIndex", ".DedupRangeMap.checkedEnd",
    ".DedupRangeMap.selectedSlice"].mapM fun suffix => do
      return mkIdent (← sourceHelper suffix)
  let names := names.toArray
  evalTactic (← `(tactic| simp only [Id.run, bind, pure, Id.instMonad,
    Except.pure, Except.bind, Except.mapError,
    ForIn.forIn, Lean.instForInLoopUnitOfMonad, $[$names:ident],*]))

elab "name_range_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``Lean.Loop.forIn)
      | throwError "no Loop.forIn found"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (← Lean.Meta.inferType body) body
    let (scan, goal) ← goal.intro1P
    let target ← goal.getType
    let target := target.replace fun expr =>
      if expr == body then some (mkFVar scan) else none
    return [← goal.change target]

theorem loop_one_update {β : Type} (f : Unit → β → Id (ForInStep β))
    (initial final : β)
    (first : f () initial = .yield final) (last : f () final = .done final) :
    Lean.Loop.forIn {} initial f = final := by
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [first, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [last, bind, pure]

variable {α : Type}

def homogeneous (capacity : UInt64) (value : α) : DedupRangeMap α :=
  ⟨#[⟨⟨0, capacity⟩, value⟩]⟩

theorem find_homogeneous (capacity offset : UInt64) (value : α)
    (inside : offset < capacity) :
    range_find_offset (homogeneous capacity value) offset = .ok 0 := by
  simp_range_helpers
  simp only [homogeneous]
  have notPast : ¬ capacity ≤ offset := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [notPast, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [bind, pure]


theorem split_singleton_zero (capacity : UInt64) (value : α) (clone : α → α) :
    range_split_index #[⟨⟨0, capacity⟩, value⟩] 0 0 clone =
      .ok (#[⟨⟨0, capacity⟩, value⟩], false) := by rfl

theorem split_singleton_stop (capacity : UInt64) (value : α) (clone : α → α) :
    range_split_index #[⟨⟨0, capacity⟩, value⟩] 0 capacity clone =
      .ok (#[⟨⟨0, capacity⟩, value⟩], false) := by
  simp_range_helpers
  simp [bind, pure, Except.bind, Except.pure]

theorem split_singleton_between (capacity finish : UInt64) (value : α)
    (positive : (0 : UInt64) < finish) (inside : finish < capacity) :
    range_split_index #[⟨⟨0, capacity⟩, value⟩] 0 finish id =
      .ok (#[⟨⟨0, finish⟩, value⟩, ⟨⟨finish, capacity⟩, value⟩], true) := by
  have nonzero : finish ≠ 0 := by
    intro equality
    subst finish
    exact (UInt64.lt_irrefl 0) positive
  have unequal : finish ≠ capacity := by
    intro equality
    subst finish
    exact (UInt64.lt_irrefl capacity) inside
  have notPast : ¬ capacity ≤ finish := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  simp [positive, nonzero, unequal, notPast, Array.insertIdx_size_self,
    bind, pure, Except.bind, Except.pure]

theorem split_second_between (offset finish capacity : UInt64) (value : α)
    (afterStart : offset < finish) (beforeEnd : finish < capacity) :
    range_split_index #[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩] 1 finish id =
      .ok (#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, finish⟩, value⟩,
        ⟨⟨finish, capacity⟩, value⟩], true) := by
  have unequalStart : finish ≠ offset := by
    intro equality
    subst finish
    exact (UInt64.lt_irrefl offset) afterStart
  have unequalEnd : finish ≠ capacity := by
    intro equality
    subst finish
    exact (UInt64.lt_irrefl capacity) beforeEnd
  have notBefore : ¬ finish < offset := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have notAfter : ¬ capacity ≤ finish := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  simp [unequalStart, unequalEnd, notBefore, notAfter, Array.insertIdx_size_self,
    bind, pure, Except.bind, Except.pure]

theorem split_second_stop (offset capacity : UInt64) (value : α) :
    range_split_index #[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩] 1 capacity id =
      .ok (#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩], false) := by
  simp_range_helpers
  simp [bind, pure, Except.bind, Except.pure]

theorem checked_end_add (offset len : UInt64)
    (fits : offset.toNat + len.toNat < 2 ^ 64) :
    range_checked_end offset len = .ok (offset + len) := by
  have noWrap : ¬ offset + len < offset := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    omega
  simp_range_helpers
  simp [Size.add, Size.ofBytes, noWrap, bind, pure, Except.bind, Except.pure, Except.mapError]

theorem checked_end_zero (capacity : UInt64) :
    range_checked_end 0 capacity = .ok capacity := by
  simp_range_helpers
  simp [Size.add, Size.ofBytes, bind, pure, Except.bind, Except.pure, Except.mapError]

theorem selected_singleton (capacity : UInt64) (value : α) :
    range_selected_slice #[⟨⟨0, capacity⟩, value⟩] 0 1 =
      .ok #[⟨⟨0, capacity⟩, value⟩] := by rfl

theorem selected_prefix_two (finish capacity : UInt64) (value : α) :
    range_selected_slice #[⟨⟨0, finish⟩, value⟩, ⟨⟨finish, capacity⟩, value⟩] 0 1 =
      .ok #[⟨⟨0, finish⟩, value⟩] := by rfl

theorem selected_middle_three (offset finish capacity : UInt64) (value : α) :
    range_selected_slice #[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, finish⟩, value⟩,
      ⟨⟨finish, capacity⟩, value⟩] 1 2 =
      .ok #[⟨⟨offset, finish⟩, value⟩] := by rfl

theorem selected_suffix_two (offset capacity : UInt64) (value : α) :
    range_selected_slice #[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩] 1 2 =
      .ok #[⟨⟨offset, capacity⟩, value⟩] := by rfl

theorem segment_at_second (offset capacity : UInt64) (value : α) :
    range_segment_at #[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩] 1 =
      some ⟨⟨offset, capacity⟩, value⟩ := by rfl

theorem segment_at_singleton (capacity : UInt64) (value : α) :
    range_segment_at #[⟨⟨0, capacity⟩, value⟩] 0 =
      some ⟨⟨0, capacity⟩, value⟩ := by rfl

theorem iter_mut_homogeneous_full [DecidableEq α] (capacity : UInt64) (value : α)
    (nonempty : capacity ≠ 0) :
    (homogeneous capacity value).iterMut Size.ZERO (Size.ofBytes capacity) =
      ⟨homogeneous capacity value, #[0], #[⟨⟨0, capacity⟩, value⟩], .ok ()⟩ := by
  have positive : (0 : UInt64) < capacity := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
    have : capacity.toNat ≠ 0 := by
      intro zero
      apply nonempty
      exact UInt64.toNat_inj.mp zero
    omega
  unfold DedupRangeMap.iterMut DedupRangeMap.iterMutWithClone
  simp only [Size.ZERO, Size.ofBytes, nonempty, beq_iff_eq, ↓reduceIte]
  rw [find_homogeneous capacity 0 value positive]
  simp only [bind, pure, Id.instMonad]
  simp only [homogeneous, split_singleton_zero, Bool.false_eq_true, ↓reduceIte]
  simp only [checked_end_zero, bind, pure, Bool.false_eq_true, ↓reduceIte]
  simp only [ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan () (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 0, 3, 0, false, none) =
      .yield (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 1, 2, 1, true, none) := by
    simp [scan, segment_at_singleton, bind, pure]
  have last : scan () (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 1, 2, 1, true, none) =
      .done (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 1, 2, 1, true, none) := by
    simp [scan, bind, pure]
  have scanDone := loop_one_update scan _ _ first last
  simp only [scanDone]
  simp [split_singleton_stop, selected_singleton, bind, pure, Except.bind, Except.pure]
  rfl

theorem iter_mut_homogeneous_prefix [DecidableEq α]
    (capacity finish : UInt64) (value : α)
    (positive : (0 : UInt64) < finish) (inside : finish < capacity) :
    (homogeneous capacity value).iterMut Size.ZERO (Size.ofBytes finish) =
      ⟨⟨#[⟨⟨0, finish⟩, value⟩, ⟨⟨finish, capacity⟩, value⟩]⟩,
        #[0], #[⟨⟨0, finish⟩, value⟩], .ok ()⟩ := by
  have capPositive : (0 : UInt64) < capacity := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have nonempty : finish ≠ 0 := by
    intro equality
    subst finish
    exact (UInt64.lt_irrefl 0) positive
  have covers : finish ≤ capacity := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  have notBefore : ¬ capacity < finish := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  unfold DedupRangeMap.iterMut DedupRangeMap.iterMutWithClone
  simp only [Size.ZERO, Size.ofBytes, nonempty, beq_iff_eq, ↓reduceIte]
  rw [find_homogeneous capacity 0 value capPositive]
  simp only [bind, pure, Id.instMonad]
  simp only [homogeneous, split_singleton_zero, Bool.false_eq_true, ↓reduceIte]
  simp only [checked_end_zero, bind, pure, Bool.false_eq_true, ↓reduceIte]
  simp only [ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan () (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 0, 3, 0, false, none) =
      .yield (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 1, 2, 1, true, none) := by
    simp [scan, segment_at_singleton, covers, notBefore, bind, pure]
  have last : scan () (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 1, 2, 1, true, none) =
      .done (⟨#[⟨⟨0, capacity⟩, value⟩]⟩, 1, 2, 1, true, none) := by
    simp [scan, bind, pure]
  have scanDone := loop_one_update scan _ _ first last
  simp only [scanDone]
  simp [split_singleton_between capacity finish value positive inside,
    selected_prefix_two, bind, pure, Except.bind, Except.pure]
  rfl

theorem iter_mut_homogeneous_interior [DecidableEq α]
    (capacity offset len : UInt64) (value : α)
    (positiveOffset : (0 : UInt64) < offset) (positiveLength : (0 : UInt64) < len)
    (interior : offset.toNat + len.toNat < capacity.toNat) :
    (homogeneous capacity value).iterMut (Size.ofBytes offset) (Size.ofBytes len) =
      ⟨⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, offset + len⟩, value⟩,
          ⟨⟨offset + len, capacity⟩, value⟩]⟩,
        #[1], #[⟨⟨offset, offset + len⟩, value⟩], .ok ()⟩ := by
  have capacityBound : capacity.toNat < 18446744073709551616 := capacity.toNat_lt_size
  have fits : offset.toNat + len.toNat < 2 ^ 64 := by omega
  have finishNat : (offset + len).toNat = offset.toNat + len.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have insideStart : offset < capacity := by
    simp only [UInt64.lt_iff_toNat_lt]
    omega
  have afterStart : offset < offset + len := by
    simp only [UInt64.lt_iff_toNat_lt, finishNat] at *
    omega
  have beforeEnd : offset + len < capacity := by
    simpa only [UInt64.lt_iff_toNat_lt, finishNat] using interior
  have covers : offset + len ≤ capacity := by
    simp only [UInt64.le_iff_toNat_le, finishNat]
    omega
  have notBefore : ¬ capacity < offset + len := by
    simp only [UInt64.lt_iff_toNat_lt, finishNat]
    omega
  have nonempty : len ≠ 0 := by
    intro equality
    subst len
    exact (UInt64.lt_irrefl 0) positiveLength
  unfold DedupRangeMap.iterMut DedupRangeMap.iterMutWithClone
  simp only [Size.ofBytes, nonempty, beq_iff_eq, ↓reduceIte]
  rw [find_homogeneous capacity offset value insideStart]
  simp only [bind, pure, Id.instMonad]
  simp only [homogeneous, split_singleton_between capacity offset value positiveOffset insideStart,
    Bool.true_eq, ↓reduceIte]
  simp only [checked_end_add offset len fits, bind, pure, Bool.false_eq_true, ↓reduceIte]
  simp only [ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan ()
      (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩, 1, 3, 1, false, none) =
      .yield (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩,
        2, 2, 2, true, none) := by
    simp [scan, segment_at_second, covers, notBefore, bind, pure]
  have last : scan ()
      (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩, 2, 2, 2, true, none) =
      .done (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩,
        2, 2, 2, true, none) := by
    simp [scan, bind, pure]
  have scanDone := loop_one_update scan _ _ first last
  simp only [scanDone]
  simp [split_second_between offset (offset + len) capacity value afterStart beforeEnd,
    selected_middle_three, bind, pure, Except.bind, Except.pure]
  rfl

theorem iter_mut_homogeneous_suffix [DecidableEq α]
    (capacity offset len : UInt64) (value : α)
    (positiveOffset : (0 : UInt64) < offset) (positiveLength : (0 : UInt64) < len)
    (fills : offset.toNat + len.toNat = capacity.toNat) :
    (homogeneous capacity value).iterMut (Size.ofBytes offset) (Size.ofBytes len) =
      ⟨⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩,
        #[1], #[⟨⟨offset, capacity⟩, value⟩], .ok ()⟩ := by
  have capacityBound : capacity.toNat < 18446744073709551616 := capacity.toNat_lt_size
  have fits : offset.toNat + len.toNat < 2 ^ 64 := by omega
  have finishEq : offset + len = capacity := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits, fills]
  have insideStart : offset < capacity := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have nonempty : len ≠ 0 := by
    intro equality
    subst len
    exact (UInt64.lt_irrefl 0) positiveLength
  unfold DedupRangeMap.iterMut DedupRangeMap.iterMutWithClone
  simp only [Size.ofBytes, nonempty, beq_iff_eq, ↓reduceIte]
  rw [find_homogeneous capacity offset value insideStart]
  simp only [bind, pure, Id.instMonad]
  simp only [homogeneous, split_singleton_between capacity offset value positiveOffset insideStart,
    Bool.true_eq, ↓reduceIte]
  simp only [checked_end_add offset len fits, finishEq, bind, pure, Bool.false_eq_true, ↓reduceIte]
  simp only [ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan ()
      (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩, 1, 3, 1, false, none) =
      .yield (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩,
        2, 2, 2, true, none) := by
    simp [scan, segment_at_second, bind, pure]
  have last : scan ()
      (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩, 2, 2, 2, true, none) =
      .done (⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩,
        2, 2, 2, true, none) := by
    simp [scan, bind, pure]
  have scanDone := loop_one_update scan _ _ first last
  simp only [scanDone]
  simp [split_second_stop, selected_suffix_two, bind, pure, Except.bind, Except.pure]
  rfl

def intervalPartition (capacity offset finish : UInt64) (value : α) : DedupRangeMap α :=
  if offset = 0 then
    if finish = capacity then homogeneous capacity value
    else ⟨#[⟨⟨0, finish⟩, value⟩, ⟨⟨finish, capacity⟩, value⟩]⟩
  else
    if finish = capacity then
      ⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, capacity⟩, value⟩]⟩
    else
      ⟨#[⟨⟨0, offset⟩, value⟩, ⟨⟨offset, finish⟩, value⟩,
        ⟨⟨finish, capacity⟩, value⟩]⟩

def intervalPosition (offset : UInt64) : Nat := if offset = 0 then 0 else 1

/-- Every nonempty in-bounds interval in a homogeneous allocation is split
exactly at its endpoints and selected once by the actual mutable iterator. -/
theorem iter_mut_homogeneous_nonempty [DecidableEq α]
    (capacity offset len : UInt64) (value : α)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (homogeneous capacity value).iterMut (Size.ofBytes offset) (Size.ofBytes len) =
      ⟨intervalPartition capacity offset (offset + len) value,
        #[intervalPosition offset], #[⟨⟨offset, offset + len⟩, value⟩], .ok ()⟩ := by
  have capacityBound : capacity.toNat < 18446744073709551616 := capacity.toNat_lt_size
  have fits : offset.toNat + len.toNat < 2 ^ 64 := by omega
  have finishNat : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  by_cases offsetZero : offset = 0
  · subst offset
    have lenLe : len.toNat ≤ capacity.toNat := by simpa using bounds
    by_cases atEnd : len = capacity
    · subst len
      have capNonzero : capacity ≠ 0 := by
        intro equality
        subst capacity
        exact (UInt64.lt_irrefl 0) positiveLength
      simpa [intervalPartition, intervalPosition, Size.ofBytes, Size.ZERO] using
        iter_mut_homogeneous_full capacity value capNonzero
    · have lenLt : len < capacity := by
        have neNat : len.toNat ≠ capacity.toNat := by
          intro equality
          exact atEnd (UInt64.toNat_inj.mp equality)
        simp only [UInt64.lt_iff_toNat_lt]
        omega
      simpa [intervalPartition, intervalPosition, atEnd, Size.ofBytes, Size.ZERO] using
        iter_mut_homogeneous_prefix capacity len value positiveLength lenLt
  · have offsetPositive : (0 : UInt64) < offset := by
      have neNat : offset.toNat ≠ 0 := by
        intro equality
        exact offsetZero (UInt64.toNat_inj.mp equality)
      simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero]
      omega
    by_cases atEnd : offset.toNat + len.toNat = capacity.toNat
    · have endEq : offset + len = capacity := by
        apply UInt64.toNat_inj.mp
        rw [finishNat, atEnd]
      simpa [intervalPartition, intervalPosition, offsetZero, endEq] using
        iter_mut_homogeneous_suffix capacity offset len value offsetPositive positiveLength atEnd
    · have strictlyInside : offset.toNat + len.toNat < capacity.toNat := by omega
      have endNe : offset + len ≠ capacity := by
        intro equality
        have equalityNat := congrArg UInt64.toNat equality
        rw [finishNat] at equalityNat
        exact atEnd equalityNat
      simpa [intervalPartition, intervalPosition, offsetZero, endNe] using
        iter_mut_homogeneous_interior capacity offset len value offsetPositive positiveLength strictlyInside

/-- Convenience form for the actual constructor used by BorrowTree.new. -/
theorem iter_mut_new_nonempty [DecidableEq α]
    (capacity offset len : UInt64) (value : α)
    (positiveLength : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (DedupRangeMap.new (Size.ofBytes capacity) value).iterMut (Size.ofBytes offset) (Size.ofBytes len) =
      ⟨intervalPartition capacity offset (offset + len) value,
        #[intervalPosition offset], #[⟨⟨offset, offset + len⟩, value⟩], .ok ()⟩ := by
  have capNonzero : capacity ≠ 0 := by
    intro equality
    subst capacity
    simp only [UInt64.lt_iff_toNat_lt] at positiveLength
    simp at bounds
    omega
  simpa [DedupRangeMap.new, homogeneous, Size.ofBytes, capNonzero] using
    iter_mut_homogeneous_nonempty capacity offset len value positiveLength bounds

abbrev divided {α : Type} (capacity boundary : UInt64) (left right : α) : DedupRangeMap α :=
  ⟨#[⟨⟨0, boundary⟩, left⟩, ⟨⟨boundary, capacity⟩, right⟩]⟩

theorem find_divided_boundary (capacity boundary : UInt64) (left right : α)
    (inside : boundary < capacity) :
    range_find_offset (divided capacity boundary left right) boundary = .ok 1 := by
  have notPast : ¬ capacity ≤ boundary := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  simp only [divided]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [notPast, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [bind, pure]

theorem split_divided_start (capacity boundary : UInt64) (left right : α) :
    range_split_index (divided capacity boundary left right).entries 1 boundary id =
      .ok ((divided capacity boundary left right).entries, false) := by
  simp_range_helpers
  simp [divided]

theorem split_divided_stop (capacity boundary : UInt64) (left right : α) :
    range_split_index (divided capacity boundary left right).entries 1 capacity id =
      .ok ((divided capacity boundary left right).entries, false) := by
  simp_range_helpers
  simp [divided]

theorem split_divided_between (capacity boundary finish : UInt64) (left right : α)
    (afterStart : boundary < finish) (beforeEnd : finish < capacity) :
    range_split_index (divided capacity boundary left right).entries 1 finish id =
      .ok (#[⟨⟨0, boundary⟩, left⟩, ⟨⟨boundary, finish⟩, right⟩,
        ⟨⟨finish, capacity⟩, right⟩], true) := by
  have unequalStart : finish ≠ boundary := by
    intro equality
    subst finish
    exact (UInt64.lt_irrefl boundary) afterStart
  have unequalEnd : finish ≠ capacity := by
    intro equality
    subst finish
    exact (UInt64.lt_irrefl capacity) beforeEnd
  have notBefore : ¬ finish < boundary := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have notAfter : ¬ capacity ≤ finish := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  simp [divided, unequalStart, unequalEnd, notBefore, notAfter, Array.insertIdx_size_self,
    bind, pure, Except.bind, Except.pure]

theorem segment_at_divided (capacity boundary : UInt64) (left right : α) :
    range_segment_at (divided capacity boundary left right).entries 1 =
      some ⟨⟨boundary, capacity⟩, right⟩ := by rfl

theorem selected_divided (capacity boundary : UInt64) (left right : α) :
    range_selected_slice (divided capacity boundary left right).entries 1 2 =
      .ok #[⟨⟨boundary, capacity⟩, right⟩] := by rfl

theorem selected_divided_middle (capacity boundary finish : UInt64) (left right : α) :
    range_selected_slice #[⟨⟨0, boundary⟩, left⟩, ⟨⟨boundary, finish⟩, right⟩,
      ⟨⟨finish, capacity⟩, right⟩] 1 2 = .ok #[⟨⟨boundary, finish⟩, right⟩] := by rfl

def dividedWindow {α : Type} (capacity boundary finish : UInt64) (left right : α) : DedupRangeMap α :=
  if finish = capacity then divided capacity boundary left right
  else ⟨#[⟨⟨0, boundary⟩, left⟩, ⟨⟨boundary, finish⟩, right⟩,
    ⟨⟨finish, capacity⟩, right⟩]⟩

/-- A range beginning at an existing two-way partition boundary selects only
its right-hand segment, even when the two payloads differ. -/
theorem iter_mut_divided_boundary [DecidableEq α]
    (capacity boundary len : UInt64) (left right : α)
    (positiveLength : (0 : UInt64) < len)
    (bounds : boundary.toNat + len.toNat ≤ capacity.toNat) :
    (divided capacity boundary left right).iterMut (Size.ofBytes boundary) (Size.ofBytes len) =
      ⟨dividedWindow capacity boundary (boundary + len) left right,
        #[1], #[⟨⟨boundary, boundary + len⟩, right⟩], .ok ()⟩ := by
  have capBound : capacity.toNat < 18446744073709551616 := capacity.toNat_lt_size
  have fits : boundary.toNat + len.toNat < 2 ^ 64 := by omega
  have finishNat : (boundary + len).toNat = boundary.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have insideStart : boundary < capacity := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have afterStart : boundary < boundary + len := by
    simp only [UInt64.lt_iff_toNat_lt, finishNat] at *
    omega
  have covers : boundary + len ≤ capacity := by
    simp only [UInt64.le_iff_toNat_le, finishNat]
    omega
  have notBefore : ¬ capacity < boundary + len := by
    simp only [UInt64.lt_iff_toNat_lt, finishNat]
    omega
  have nonempty : len ≠ 0 := by
    intro equality
    subst len
    exact (UInt64.lt_irrefl 0) positiveLength
  unfold DedupRangeMap.iterMut DedupRangeMap.iterMutWithClone
  simp only [Size.ofBytes, nonempty, beq_iff_eq, ↓reduceIte]
  rw [find_divided_boundary capacity boundary left right insideStart]
  simp only [bind, pure, Id.instMonad]
  rw [split_divided_start capacity boundary left right]
  simp only [Bool.false_eq_true, ↓reduceIte]
  simp only [checked_end_add boundary len fits, bind, pure, Bool.false_eq_true, ↓reduceIte]
  simp only [ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have first : scan () (divided capacity boundary left right, 1, 3, 1, false, none) =
      .yield (divided capacity boundary left right, 2, 2, 2, true, none) := by
    simp only [scan]
    rw [segment_at_divided capacity boundary left right]
    simp [divided, covers, notBefore, bind, pure]
  have last : scan () (divided capacity boundary left right, 2, 2, 2, true, none) =
      .done (divided capacity boundary left right, 2, 2, 2, true, none) := by
    simp [scan, bind, pure]
  have scanDone := loop_one_update scan _ _ first last
  simp only [scanDone]
  by_cases atEnd : boundary + len = capacity
  · simp only [dividedWindow, atEnd, ↓reduceIte]
    rw [split_divided_stop capacity boundary left right]
    dsimp only
    rw [selected_divided capacity boundary left right]
    simp [Id.run, divided]
  · have beforeEnd : boundary + len < capacity := by
      have neNat : (boundary + len).toNat ≠ capacity.toNat := by
        intro equality
        exact atEnd (UInt64.toNat_inj.mp equality)
      simp only [UInt64.lt_iff_toNat_lt, finishNat] at *
      omega
    simp only [dividedWindow, atEnd, ↓reduceIte]
    rw [split_divided_between capacity boundary (boundary + len) left right afterStart beforeEnd]
    dsimp only
    rw [selected_divided_middle capacity boundary (boundary + len) left right]
    simp [Id.run]

/-- Exact source iterator behavior when the requested interval is one existing
stored segment. Primitive lookup/split facts are discharged by callers from
explicit partition structure; the loop itself is proved here. -/
theorem iter_mut_existing_segment [DecidableEq α]
    (map : DedupRangeMap α) (offset len : Size) (finish : UInt64) (index : Nat) (value : α)
    (nonempty : len.bytes ≠ 0)
    (search : range_find_offset map offset.bytes = .ok index)
    (startSplit : range_split_index map.entries index offset.bytes id = .ok (map.entries, false))
    (finishCalc : range_checked_end offset.bytes len.bytes = .ok finish)
    (selected : range_segment_at map.entries index = some ⟨⟨offset.bytes, finish⟩, value⟩)
    (endSplit : range_split_index map.entries index finish id = .ok (map.entries, false))
    (slice : range_selected_slice map.entries index (index + 1) =
      .ok #[⟨⟨offset.bytes, finish⟩, value⟩]) :
    map.iterMut offset len = ⟨map, #[index], #[⟨⟨offset.bytes, finish⟩, value⟩], .ok ()⟩ := by
  unfold DedupRangeMap.iterMut DedupRangeMap.iterMutWithClone
  simp only [nonempty, beq_iff_eq, ↓reduceIte]
  rw [search]
  simp only [bind, pure, Id.instMonad]
  rw [startSplit]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [finishCalc]
  simp only [bind, pure, Id.instMonad, ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have removed : index + 1 - index - 1 = 0 := by omega
  have lastIndex : index + 1 - 1 = index := by omega
  have count : index + 1 - index = 1 := by omega
  have first : scan () (map, index, 3, index, false, none) =
      .yield (map, index + 1, 2, index + 1, true, none) := by
    simp only [scan]
    rw [selected]
    simp [removed, bind, pure]
  have last : scan () (map, index + 1, 2, index + 1, true, none) =
      .done (map, index + 1, 2, index + 1, true, none) := by
    simp [scan, bind, pure]
  have scanDone := loop_one_update scan _ _ first last
  simp only [scanDone, lastIndex]
  rw [endSplit]
  dsimp only
  rw [slice]
  simp [Id.run, count, lastIndex]

/-- A nonempty request beginning at a stored boundary and ending inside that
same segment. The endpoint split may insert one new boundary. -/
theorem iter_mut_segment_prefix [DecidableEq α]
    (map result : DedupRangeMap α) (offset len : Size) (finish segmentEnd : UInt64)
    (index : Nat) (value : α) (inserted : Bool)
    (nonempty : len.bytes ≠ 0)
    (search : range_find_offset map offset.bytes = .ok index)
    (startSplit : range_split_index map.entries index offset.bytes id = .ok (map.entries, false))
    (finishCalc : range_checked_end offset.bytes len.bytes = .ok finish)
    (selected : range_segment_at map.entries index = some ⟨⟨offset.bytes, segmentEnd⟩, value⟩)
    (covers : finish ≤ segmentEnd)
    (endSplit : range_split_index map.entries index finish id = .ok (result.entries, inserted))
    (slice : range_selected_slice result.entries index (index + 1) =
      .ok #[⟨⟨offset.bytes, finish⟩, value⟩]) :
    map.iterMut offset len = ⟨result, #[index], #[⟨⟨offset.bytes, finish⟩, value⟩], .ok ()⟩ := by
  have notBefore : ¬ segmentEnd < finish := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le] at *
    omega
  unfold DedupRangeMap.iterMut DedupRangeMap.iterMutWithClone
  simp only [nonempty, beq_iff_eq, ↓reduceIte]
  rw [search]
  simp only [bind, pure, Id.instMonad]
  rw [startSplit]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [finishCalc]
  simp only [bind, pure, Id.instMonad, ForIn.forIn, Lean.instForInLoopUnitOfMonad]
  name_range_scan
  have removed : index + 1 - index - 1 = 0 := by omega
  have lastIndex : index + 1 - 1 = index := by omega
  have count : index + 1 - index = 1 := by omega
  have first : scan () (map, index, 3, index, false, none) =
      .yield (map, index + 1, 2, index + 1, true, none) := by
    simp only [scan]
    rw [selected]
    simp [removed, covers, notBefore, bind, pure]
  have last : scan () (map, index + 1, 2, index + 1, true, none) =
      .done (map, index + 1, 2, index + 1, true, none) := by
    simp [scan, bind, pure]
  have scanDone := loop_one_update scan _ _ first last
  simp only [scanDone, lastIndex]
  rw [endSplit]
  dsimp only
  rw [slice]
  cases result
  simp [Id.run, count, lastIndex]

#print axioms iter_mut_segment_prefix
#print axioms find_homogeneous
#print axioms iter_mut_homogeneous_full
#print axioms iter_mut_homogeneous_prefix
#print axioms iter_mut_homogeneous_interior
#print axioms iter_mut_homogeneous_suffix
#print axioms iter_mut_homogeneous_nonempty
#print axioms iter_mut_new_nonempty
#print axioms find_divided_boundary
#print axioms iter_mut_divided_boundary
#print axioms iter_mut_existing_segment

end DuplicatePrefix.RangeMapNonempty
