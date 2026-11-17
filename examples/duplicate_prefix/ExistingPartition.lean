import duplicate_prefix.RangeMapNonempty
import duplicate_prefix.PartitionFind

/-! Reusing an existing stored interval through the actual mutable iterator. -/
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace DuplicatePrefix.ExistingPartition
open Miri.ABI Miri.DataStructures
open RangeMapNonempty

theorem start_split {α : Type} (capacity offset finish : UInt64) (value : α) :
    range_split_index (intervalPartition capacity offset finish value).entries
      (intervalPosition offset) offset id =
      .ok ((intervalPartition capacity offset finish value).entries, false) := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;>
    simp_all [intervalPartition, intervalPosition, homogeneous, bind, pure,
      Except.bind, Except.pure]

theorem end_split {α : Type} (capacity offset finish : UInt64) (value : α) :
    range_split_index (intervalPartition capacity offset finish value).entries
      (intervalPosition offset) finish id =
      .ok ((intervalPartition capacity offset finish value).entries, false) := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;>
    simp_all [intervalPartition, intervalPosition, homogeneous, bind, pure,
      Except.bind, Except.pure]

theorem segment {α : Type} (capacity offset finish : UInt64) (value : α) :
    range_segment_at (intervalPartition capacity offset finish value).entries
      (intervalPosition offset) = some ⟨⟨offset, finish⟩, value⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;>
    simp_all [intervalPartition, intervalPosition, homogeneous, bind, pure,
      Except.bind, Except.pure]

theorem slice {α : Type} (capacity offset finish : UInt64) (value : α) :
    range_selected_slice (intervalPartition capacity offset finish value).entries
      (intervalPosition offset) (intervalPosition offset + 1) =
      .ok #[⟨⟨offset, finish⟩, value⟩] := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;>
    simp_all [intervalPartition, intervalPosition, homogeneous, bind, pure,
      Except.bind, Except.pure]

theorem iterMut_intervalPartition {α : Type} [DecidableEq α]
    (capacity offset len : UInt64) (value : α)
    (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat) :
    (intervalPartition capacity offset (offset + len) value).iterMut
      (Size.ofBytes offset) (Size.ofBytes len) =
      ⟨intervalPartition capacity offset (offset + len) value,
        #[intervalPosition offset], #[⟨⟨offset, offset + len⟩, value⟩], .ok ()⟩ := by
  have nonzero : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  have fits : offset.toNat + len.toNat < 2 ^ 64 := by
    have limit := capacity.toNat_lt
    omega
  have finishNat : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have inside : offset < offset + len := by
    simp only [UInt64.lt_iff_toNat_lt, finishNat] at *
    omega
  have finishPositive : (0 : UInt64) < offset + len := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero, finishNat] at *
    omega
  have search : range_find_offset
      (intervalPartition capacity offset (offset + len) value) offset =
      .ok (intervalPosition offset) := by
    by_cases start : offset = 0
    · by_cases stop : offset + len = capacity
      · have capPositive : (0 : UInt64) < capacity := by simpa [stop] using finishPositive
        simp only [start, UInt64.zero_add] at stop
        simpa [intervalPartition, intervalPosition, start, stop] using
          find_homogeneous capacity 0 value capPositive
      · simp only [start, UInt64.zero_add] at stop
        simpa [intervalPartition, intervalPosition, start, stop, divided] using
          PartitionFind.find_divided_first capacity (offset + len) value value finishPositive
    · by_cases stop : offset + len = capacity
      · have beforeCapacity : offset < capacity := by simpa [stop] using inside
        simpa [intervalPartition, intervalPosition, start, stop, divided] using
          find_divided_boundary capacity offset value value beforeCapacity
      · simpa [intervalPartition, intervalPosition, start, stop] using
          PartitionFind.find_triple_middle offset (offset + len) capacity value value value inside
  exact iter_mut_existing_segment
    (intervalPartition capacity offset (offset + len) value)
    (Size.ofBytes offset) (Size.ofBytes len) (offset + len) (intervalPosition offset) value
    nonzero search (start_split capacity offset (offset + len) value)
    (checked_end_add offset len fits) (segment capacity offset (offset + len) value)
    (end_split capacity offset (offset + len) value) (slice capacity offset (offset + len) value)

#print axioms iterMut_intervalPartition

end DuplicatePrefix.ExistingPartition

open Lean Elab Command in
run_cmd do
  let declaration := ``DuplicatePrefix.ExistingPartition.iterMut_intervalPartition
  for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "{declaration} depends on unapproved axiom {dependency}"
