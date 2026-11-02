import Miri.Memory.Access

/-! Component proofs for duplicate_prefix. These establish arithmetic and the
actual allocation-bounds checks, not whole-interpreter safety. All offsets are
allocation-relative; the slice need not start at offset zero. -/

namespace DuplicatePrefix
open Miri.ABI Miri.Memory

theorem copy_fits {length n : Nat} (guard : n ≤ length / 2) :
    n + n ≤ length := by omega

/-- Connect the 64-bit unsigned guard to the natural-number range lemma. -/
theorem usize_guard {length n : UInt64} (guard : ¬ n > length / 2) :
    n.toNat + n.toNat ≤ length.toNat := by
  have guardNat : n.toNat ≤ length.toNat / 2 := by
    simpa [UInt64.lt_iff_toNat_lt] using guard
  exact copy_fits guardNat

/-- Checked addition cannot wrap when the natural-number sum fits u64. -/
theorem size_add_ok (left right : Size)
    (fits : left.bytes.toNat + right.bytes.toNat < 2 ^ 64) :
    Size.add left right = .ok (Size.ofBytes (left.bytes + right.bytes)) := by
  have noWrap : ¬ left.bytes + right.bytes < left.bytes := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, Nat.mod_eq_of_lt fits]
    omega
  simp [Size.add, noWrap]

/-- The one-copy size multiplication performed by the memory-copy path
cannot overflow, even at the maximum representable byte count. -/
theorem size_mul_one (size : Size) : Size.mul size 1 = .ok size := by
  cases size
  simp [Size.mul, Size.ofBytes]

/-- Conversion to the signed access-size representation is also checked by
the real library operation. -/
theorem signed_size_ok (size : Size)
    (fits : size.bytes.toNat < 9223372036854775808) :
    sizeAsI64 size = .ok (Int.ofNat size.bytes.toNat) := by
  simp [sizeAsI64, fits]

/-- Compute the real checked source endpoint; this is the destination offset
required for the nonoverlapping copy. -/
theorem source_end (source : Size) (n : UInt64)
    (fits : source.bytes.toNat + n.toNat < 2 ^ 64) :
    (allocRange source (Size.ofBytes n)).endExclusive =
      .ok (Size.ofBytes (source.bytes + n)) := by
  unfold AllocRange.endExclusive AllocRange.end allocRange
  rw [size_add_ok source (Size.ofBytes n) fits]
  rfl

/-- The overlap predicate in Allocation.copyRepeatedly is false when the
destination is the checked exclusive source endpoint. -/
theorem adjacent_overlap_check (source sourceFinish destinationFinish : Size) (n : UInt64)
    (fits : source.bytes.toNat + n.toNat < 2 ^ 64)
    (endpoint : (allocRange source (Size.ofBytes n)).endExclusive = .ok sourceFinish) :
    ((source.bytes < destinationFinish.bytes) &&
      ((source.bytes + n) < sourceFinish.bytes)) = false := by
  rw [source_end source n fits] at endpoint
  have eq : Size.ofBytes (source.bytes + n) = sourceFinish := Except.ok.inj endpoint
  subst sourceFinish
  simp [Size.ofBytes]

theorem copy_intervals {base length n capacity : Nat}
    (sliceFits : base + length ≤ capacity) (guard : n ≤ length / 2) :
    base + n ≤ capacity ∧ base + n + n ≤ capacity ∧
      (∀ index, base ≤ index → index < base + n →
        ¬ (base + n ≤ index ∧ index < base + n + n)) := by
  have := copy_fits guard
  refine ⟨by omega, by omega, ?_⟩
  intro index lower upper
  omega

/-- The actual lean-miri bounds checker accepts any nonnegative in-bounds
interval whose size fits its signed host representation. -/
theorem checkedBounds_ok (target : PointerArithmetic) (id : AllocId)
    (capacity offset : Size) (count : Nat) (message : CheckInAllocMsg)
    (signedFits : count < 9223372036854775808)
    (inBounds : offset.bytes.toNat + count ≤ capacity.bytes.toNat) :
    checkedBounds target id capacity offset (Int.ofNat count) message = .ok () := by
  simp [checkedBounds]
  split
  · rename_i badSize
    change (decide (-(2 ^ 63 : Int) ≤ (count : Int)) &&
      decide ((count : Int) < (2 ^ 63 : Int))) = false at badSize
    simp at badSize
    omega
  · simp [Nat.not_lt.mpr inBounds]
    rfl

/-- Both real allocation-bounds checks for the copy, with the destination
offset supplied by the pointer-resolution layer. Provenance/permissions are
separate obligations. -/
theorem copy_bounds_ok (target : PointerArithmetic) (id : AllocId)
    (capacity source destination : Size) (length n : Nat)
    (sliceFits : source.bytes.toNat + length ≤ capacity.bytes.toNat)
    (guard : n ≤ length / 2)
    (signedFits : n < 9223372036854775808)
    (destinationOffset : destination.bytes.toNat = source.bytes.toNat + n) :
    checkedBounds target id capacity source (Int.ofNat n) .memoryAccess = .ok () ∧
    checkedBounds target id capacity destination (Int.ofNat n) .memoryAccess = .ok () := by
  have fits := copy_fits guard
  constructor
  · apply checkedBounds_ok <;> omega
  · apply checkedBounds_ok <;> omega

/-- Derive both bounds checks and the checked source endpoint directly from
the unsigned guard and a slice region. No destination-offset or count-size
conclusion is assumed. This remains a component theorem: resolving pointers
and establishing access permissions belong to the interpreter connection. -/
theorem guarded_copy_checks (target : PointerArithmetic) (id : AllocId)
    (capacity source : Size) (length n : UInt64)
    (sliceFits : source.bytes.toNat + length.toNat ≤ capacity.bytes.toNat)
    (lengthFits : length.toNat < 9223372036854775808)
    (guard : ¬ n > length / 2) :
    let destination := Size.ofBytes (source.bytes + n)
    checkedBounds target id capacity source (Int.ofNat n.toNat) .memoryAccess = .ok () ∧
    checkedBounds target id capacity destination (Int.ofNat n.toNat) .memoryAccess = .ok () ∧
    (allocRange source (Size.ofBytes n)).endExclusive = .ok destination := by
  dsimp only
  have countFits := usize_guard guard
  have capacityFits : capacity.bytes.toNat < 18446744073709551616 :=
    capacity.bytes.toNat_lt_size
  have sumFits : source.bytes.toNat + n.toNat < 2 ^ 64 := by omega
  have destinationOffset : (Size.ofBytes (source.bytes + n)).bytes.toNat =
      source.bytes.toNat + n.toNat := by
    simp [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt sumFits]
  refine ⟨?_, ?_, source_end source n sumFits⟩
  · apply checkedBounds_ok <;> omega
  · apply checkedBounds_ok <;> omega

end DuplicatePrefix
