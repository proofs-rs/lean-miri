import duplicate_prefix.RangeMapNonempty
import Init.Internal.Order.While

/-! Concrete binary-search facts for the interval partitions produced by
`DedupRangeMap.iterMut`. These unfold the actual `findOffset` loop. -/

namespace DuplicatePrefix.PartitionFind

open Miri.ABI Miri.DataStructures
open DuplicatePrefix.RangeMapNonempty

variable {α : Type}

theorem find_divided_first (capacity boundary : UInt64) (left right : α)
    (positive : (0 : UInt64) < boundary) :
    range_find_offset (divided capacity boundary left right) 0 = .ok 0 := by
  have notPast : ¬ boundary ≤ (0 : UInt64) := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  have nonzero : boundary ≠ 0 := by
    intro equality
    subst boundary
    exact (UInt64.lt_irrefl 0) positive
  simp_range_helpers
  simp only [divided]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [positive, notPast, nonzero, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [positive, notPast, nonzero, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [bind, pure]

theorem find_triple_middle (offset finish capacity : UInt64) (a b c : α)
    (inside : offset < finish) :
    range_find_offset
      ⟨#[⟨⟨0, offset⟩, a⟩, ⟨⟨offset, finish⟩, b⟩, ⟨⟨finish, capacity⟩, c⟩]⟩
      offset = .ok 1 := by
  have stopNotLe : ¬ finish ≤ offset := by
    simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt] at *
    omega
  simp_range_helpers
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [inside, stopNotLe, bind, pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp [inside, stopNotLe, bind, pure]

#print axioms find_divided_first
#print axioms find_triple_middle

end DuplicatePrefix.PartitionFind
