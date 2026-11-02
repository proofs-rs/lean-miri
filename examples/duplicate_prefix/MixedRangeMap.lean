import duplicate_prefix.BorrowRangeAccess
import duplicate_prefix.PartitionFind

namespace DuplicatePrefix.MixedRangeMap
open Miri.ABI Miri.DataStructures
open RangeMapNonempty BorrowRangeAccess
variable {α : Type}

def splitInside (capacity offset finish pivot : UInt64) (outside inside : α) : DedupRangeMap α :=
  if offset = 0 then
    if finish = capacity then
      ⟨#[⟨⟨0, pivot⟩, inside⟩, ⟨⟨pivot, capacity⟩, inside⟩]⟩
    else ⟨#[⟨⟨0, pivot⟩, inside⟩, ⟨⟨pivot, finish⟩, inside⟩, ⟨⟨finish, capacity⟩, outside⟩]⟩
  else if finish = capacity then
    ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, pivot⟩, inside⟩, ⟨⟨pivot, capacity⟩, inside⟩]⟩
  else ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, pivot⟩, inside⟩,
    ⟨⟨pivot, finish⟩, inside⟩, ⟨⟨finish, capacity⟩, outside⟩]⟩

theorem initial_search (capacity offset finish : UInt64) (outside inside : α)
    (positive : offset < finish) :
    range_find_offset (partitionWithInside capacity offset finish outside inside) offset =
      .ok (intervalPosition offset) := by
  by_cases start : offset = 0
  · by_cases stop : finish = capacity
    · have capPositive : (0 : UInt64) < capacity := by simpa [start, stop] using positive
      simpa [partitionWithInside, intervalPosition, homogeneous, start, stop] using
        find_homogeneous capacity 0 inside capPositive
    · have finishPositive : (0 : UInt64) < finish := by simpa [start] using positive
      simpa [partitionWithInside, intervalPosition, start, stop, divided] using
        PartitionFind.find_divided_first capacity finish inside outside finishPositive
  · by_cases stop : finish = capacity
    · have beforeCapacity : offset < capacity := by simpa [stop] using positive
      simpa [partitionWithInside, intervalPosition, start, stop, divided] using
        find_divided_boundary capacity offset outside inside beforeCapacity
    · simpa [partitionWithInside, intervalPosition, start, stop] using
        PartitionFind.find_triple_middle offset finish capacity outside inside outside positive

theorem initial_start (capacity offset finish : UInt64) (outside inside : α) :
    range_split_index (partitionWithInside capacity offset finish outside inside).entries
      (intervalPosition offset) offset id =
      .ok ((partitionWithInside capacity offset finish outside inside).entries, false) := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;> simp_all [partitionWithInside, intervalPosition, homogeneous]

theorem initial_segment (capacity offset finish : UInt64) (outside inside : α) :
    range_segment_at (partitionWithInside capacity offset finish outside inside).entries
      (intervalPosition offset) = some ⟨⟨offset, finish⟩, inside⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;> simp_all [partitionWithInside, intervalPosition, homogeneous]

theorem initial_end_split (capacity offset finish pivot : UInt64) (outside inside : α)
    (afterStart : offset < pivot) (beforeEnd : pivot < finish) :
    range_split_index (partitionWithInside capacity offset finish outside inside).entries
      (intervalPosition offset) pivot id =
      .ok ((splitInside capacity offset finish pivot outside inside).entries, true) := by
  have startNe : pivot ≠ offset := by intro h; subst pivot; exact (UInt64.lt_irrefl offset) afterStart
  have endNe : pivot ≠ finish := by intro h; subst pivot; exact (UInt64.lt_irrefl finish) beforeEnd
  have startLe : offset ≤ pivot := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  have endNotLe : ¬ finish ≤ pivot := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;>
    simp_all [partitionWithInside, splitInside, intervalPosition, homogeneous, bind, pure, Except.bind, Except.pure]

theorem split_slice (capacity offset finish pivot : UInt64) (outside inside : α) :
    range_selected_slice (splitInside capacity offset finish pivot outside inside).entries
      (intervalPosition offset) (intervalPosition offset + 1) = .ok #[⟨⟨offset, pivot⟩, inside⟩] := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;> simp_all [splitInside, intervalPosition]

theorem iterMut_initial_prefix [DecidableEq α]
    (capacity offset len finish : UInt64) (outside inside : α)
    (positive : (0 : UInt64) < len)
    (interior : offset.toNat + len.toNat < finish.toNat) :
    (partitionWithInside capacity offset finish outside inside).iterMut
      (Size.ofBytes offset) (Size.ofBytes len) =
      ⟨splitInside capacity offset finish (offset + len) outside inside,
        #[intervalPosition offset], #[⟨⟨offset, offset + len⟩, inside⟩], .ok ()⟩ := by
  have fits : offset.toNat + len.toNat < 2^64 := by have limit := finish.toNat_lt; omega
  have finishNat : (offset + len).toNat = offset.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have afterStart : offset < offset + len := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero, finishNat] at *
    omega
  have beforeEnd : offset + len < finish := by simpa only [UInt64.lt_iff_toNat_lt, finishNat] using interior
  have beforeFinish : offset < finish := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  have covers : offset + len ≤ finish := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  have nonempty : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  exact iter_mut_segment_prefix
    (partitionWithInside capacity offset finish outside inside)
    (splitInside capacity offset finish (offset + len) outside inside)
    (Size.ofBytes offset) (Size.ofBytes len) (offset + len) finish
    (intervalPosition offset) inside true nonempty
    (initial_search capacity offset finish outside inside beforeFinish)
    (initial_start capacity offset finish outside inside)
    (checked_end_add offset len fits)
    (initial_segment capacity offset finish outside inside) covers
    (initial_end_split capacity offset finish (offset + len) outside inside afterStart beforeEnd)
    (split_slice capacity offset finish (offset + len) outside inside)

theorem find_three_last (offset pivot finish : UInt64) (a b c : α)
    (positive : offset < pivot) (inside : pivot < finish) :
    range_find_offset ⟨#[⟨⟨0, offset⟩, a⟩, ⟨⟨offset, pivot⟩, b⟩,
      ⟨⟨pivot, finish⟩, c⟩]⟩ pivot = .ok 2 := by
  have noEnd : ¬ finish ≤ pivot := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  have noEarlier : ¬ pivot < offset := by
    simp only [UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [positive, inside, noEnd, noEarlier, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [positive, inside, noEnd, noEarlier, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [bind, pure]

theorem find_four_third (offset pivot finish capacity : UInt64) (a b c d : α)
    (inside : pivot < finish) :
    range_find_offset ⟨#[⟨⟨0, offset⟩, a⟩, ⟨⟨offset, pivot⟩, b⟩,
      ⟨⟨pivot, finish⟩, c⟩, ⟨⟨finish, capacity⟩, d⟩]⟩ pivot = .ok 2 := by
  have noEnd : ¬ finish ≤ pivot := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [inside, noEnd, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [bind, pure]

def secondPosition (offset : UInt64) := intervalPosition offset + 1

theorem second_search (capacity offset finish pivot : UInt64) (outside inside : α)
    (afterStart : offset < pivot) (beforeEnd : pivot < finish) :
    range_find_offset (splitInside capacity offset finish pivot outside inside) pivot =
      .ok (secondPosition offset) := by
  by_cases start : offset = 0
  · by_cases stop : finish = capacity
    · have beforeCapacity : pivot < capacity := by simpa [stop] using beforeEnd
      simpa [splitInside, secondPosition, intervalPosition, start, stop, divided] using
        find_divided_boundary capacity pivot inside inside beforeCapacity
    · simpa [splitInside, secondPosition, intervalPosition, start, stop] using
        PartitionFind.find_triple_middle pivot finish capacity inside inside outside beforeEnd
  · by_cases stop : finish = capacity
    · have beforeCapacity : pivot < capacity := by simpa [stop] using beforeEnd
      simpa [splitInside, secondPosition, intervalPosition, start, stop] using
        find_three_last offset pivot capacity outside inside inside afterStart beforeCapacity
    · simpa [splitInside, secondPosition, intervalPosition, start, stop] using
        find_four_third offset pivot finish capacity outside inside inside outside beforeEnd

def doubleSplit (capacity offset finish first second : UInt64) (outside left middle right : α) :
    DedupRangeMap α :=
  if offset = 0 then
    if second = finish then
      if finish = capacity then ⟨#[⟨⟨0, first⟩, left⟩, ⟨⟨first, capacity⟩, middle⟩]⟩
      else ⟨#[⟨⟨0, first⟩, left⟩, ⟨⟨first, finish⟩, middle⟩, ⟨⟨finish, capacity⟩, outside⟩]⟩
    else if finish = capacity then
      ⟨#[⟨⟨0, first⟩, left⟩, ⟨⟨first, second⟩, middle⟩, ⟨⟨second, capacity⟩, right⟩]⟩
    else ⟨#[⟨⟨0, first⟩, left⟩, ⟨⟨first, second⟩, middle⟩,
      ⟨⟨second, finish⟩, right⟩, ⟨⟨finish, capacity⟩, outside⟩]⟩
  else if second = finish then
    if finish = capacity then
      ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, first⟩, left⟩, ⟨⟨first, capacity⟩, middle⟩]⟩
    else ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, first⟩, left⟩,
      ⟨⟨first, finish⟩, middle⟩, ⟨⟨finish, capacity⟩, outside⟩]⟩
  else if finish = capacity then
    ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, first⟩, left⟩,
      ⟨⟨first, second⟩, middle⟩, ⟨⟨second, capacity⟩, right⟩]⟩
  else ⟨#[⟨⟨0, offset⟩, outside⟩, ⟨⟨offset, first⟩, left⟩,
    ⟨⟨first, second⟩, middle⟩, ⟨⟨second, finish⟩, right⟩, ⟨⟨finish, capacity⟩, outside⟩]⟩

theorem second_start (capacity offset finish first : UInt64) (outside inside : α) :
    range_split_index (splitInside capacity offset finish first outside inside).entries
      (secondPosition offset) first id =
      .ok ((splitInside capacity offset finish first outside inside).entries, false) := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;> simp_all [splitInside, secondPosition, intervalPosition]

theorem second_segment (capacity offset finish first : UInt64) (outside inside : α) :
    range_segment_at (splitInside capacity offset finish first outside inside).entries
      (secondPosition offset) = some ⟨⟨first, finish⟩, inside⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_helpers <;> simp_all [splitInside, secondPosition, intervalPosition]

theorem second_end_split (capacity offset finish first second : UInt64) (outside inside : α)
    (afterStart : first < second) (beforeEnd : second ≤ finish) :
    range_split_index (splitInside capacity offset finish first outside inside).entries
      (secondPosition offset) second id =
      .ok ((doubleSplit capacity offset finish first second outside inside inside inside).entries,
        if second = finish then false else true) := by
  have firstNe : second ≠ first := by intro h; subst second; exact (UInt64.lt_irrefl first) afterStart
  have startLe : first ≤ second := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  have notPast : second ≠ finish → ¬ finish ≤ second := by
    intro ne le
    have natNe : second.toNat ≠ finish.toNat := by
      intro h
      exact ne (UInt64.toNat_inj.mp h)
    simp only [UInt64.le_iff_toNat_le] at *
    omega
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    by_cases cut : second = finish <;>
    simp_range_helpers <;>
    simp_all [splitInside, doubleSplit, secondPosition, intervalPosition,
      UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, bind, pure, Except.bind, Except.pure] <;> omega

theorem second_slice (capacity offset finish first second : UInt64) (outside inside : α) :
    range_selected_slice (doubleSplit capacity offset finish first second outside inside inside inside).entries
      (secondPosition offset) (secondPosition offset + 1) = .ok #[⟨⟨first, second⟩, inside⟩] := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    by_cases cut : second = finish <;>
    simp_range_helpers <;> simp_all [doubleSplit, secondPosition, intervalPosition]

theorem split_set_same (capacity offset finish first : UInt64) (outside inside : α) :
    (splitInside capacity offset finish first outside inside).setAtPos (intervalPosition offset) inside =
      ⟨splitInside capacity offset finish first outside inside, .ok ()⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    simp_range_updates <;> simp_all [splitInside, intervalPosition]

theorem double_set_middle (capacity offset finish first second : UInt64)
    (outside inside replacement : α) :
    (doubleSplit capacity offset finish first second outside inside inside inside).setAtPos
      (secondPosition offset) replacement =
      ⟨doubleSplit capacity offset finish first second outside inside replacement inside, .ok ()⟩ := by
  by_cases start : offset = 0 <;> by_cases stop : finish = capacity <;>
    by_cases cut : second = finish <;>
    simp_range_updates <;> simp_all [doubleSplit, secondPosition, intervalPosition]

theorem iterMut_second_prefix [DecidableEq α]
    (capacity offset finish first len : UInt64) (outside inside : α)
    (positive : (0 : UInt64) < len) (afterStart : offset < first)
    (beforeEnd : first.toNat + len.toNat ≤ finish.toNat) :
    (splitInside capacity offset finish first outside inside).iterMut
      (Size.ofBytes first) (Size.ofBytes len) =
      ⟨doubleSplit capacity offset finish first (first + len) outside inside inside inside,
        #[secondPosition offset], #[⟨⟨first, first + len⟩, inside⟩], .ok ()⟩ := by
  have fits : first.toNat + len.toNat < 2^64 := by have limit := finish.toNat_lt; omega
  have finishNat : (first + len).toNat = first.toNat + len.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have afterFirst : first < first + len := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero, finishNat] at *
    omega
  have covers : first + len ≤ finish := by simpa only [UInt64.le_iff_toNat_le, finishNat] using beforeEnd
  have firstInside : first < finish := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  have nonempty : len ≠ 0 := by intro h; subst len; exact (UInt64.lt_irrefl 0) positive
  exact iter_mut_segment_prefix
    (splitInside capacity offset finish first outside inside)
    (doubleSplit capacity offset finish first (first + len) outside inside inside inside)
    (Size.ofBytes first) (Size.ofBytes len) (first + len) finish
    (secondPosition offset) inside (if first + len = finish then false else true) nonempty
    (second_search capacity offset finish first outside inside afterStart firstInside)
    (second_start capacity offset finish first outside inside)
    (checked_end_add first len fits)
    (second_segment capacity offset finish first outside inside) covers
    (second_end_split capacity offset finish first (first + len) outside inside afterFirst covers)
    (second_slice capacity offset finish first (first + len) outside inside)

#print axioms split_set_same
#print axioms double_set_middle
#print axioms iterMut_second_prefix
#print axioms second_start
#print axioms second_segment
#print axioms second_end_split
#print axioms second_slice
#print axioms find_three_last
#print axioms find_four_third
#print axioms second_search
#print axioms iterMut_initial_prefix
#print axioms initial_search
#print axioms initial_start
#print axioms initial_segment
#print axioms initial_end_split
#print axioms split_slice
end DuplicatePrefix.MixedRangeMap
