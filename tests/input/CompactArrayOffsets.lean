import Miri.Input.TableCore
import Miri.Input.RuntimeMetadata

open Miri Miri.ABI Miri.Input Miri.Interpreter

/-- The endpoint check covers every permitted source index, not just sampled
offsets. Nat multiplication avoids wraparound in the validator itself. -/
theorem array_formula_all_indices_fit (stride count index : Nat)
    (endpoint : count = 0 ∨ stride * (count - 1) < 2^64) (inside : index < count) :
    stride * index < 2^64 := by
  have bound : index ≤ count - 1 := by omega
  have last : stride * (count - 1) < 2^64 := by
    rcases endpoint with empty | last
    · omega
    · exact last
  exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left stride bound) last

/-- The runtime's complete array offset function remains the pinned checked
stride multiplication for all indices; no explicit offset vector is needed. -/
theorem array_formula_runtime_offset (stride : Size) (count : UInt64) (index : Nat) :
    (FieldsShape.Array stride count).offset index =
      if index ≥ count.toNat then .error (.fieldOutOfBounds index count.toNat)
      else (stride.mul (UInt64.ofNat index)).mapError LayoutError.size := by
  rfl

/-- Every validated formula index returns the exact mathematical offset from
the runtime's existing checked-u64 operation, with no wrapping or exhaustion. -/
theorem array_formula_runtime_value (stride : Size) (count index : UInt64)
    (endpoint : count.toNat = 0 ∨ stride.bytes.toNat * (count.toNat - 1) < 2^64)
    (inside : index.toNat < count.toNat) :
    (FieldsShape.Array stride count).offset index.toNat =
      .ok (Size.ofBytes (UInt64.ofNat (stride.bytes.toNat * index.toNat))) := by
  have fits := array_formula_all_indices_fit stride.bytes.toNat count.toNat index.toNat endpoint inside
  have product : (stride.bytes * index).toNat = stride.bytes.toNat * index.toNat := by
    rw [UInt64.toNat_mul, Nat.mod_eq_of_lt fits]
  have exactProduct : stride.bytes * index = UInt64.ofNat (stride.bytes.toNat * index.toNat) := by
    apply UInt64.toNat_inj.mp
    simp [Nat.mod_eq_of_lt fits]
  rw [array_formula_runtime_offset]
  simp only [UInt64.ofNat_toNat, ge_iff_le, Nat.not_le.mpr inside, ↓reduceIte]
  by_cases zero : index = 0
  · simp [Size.mul, zero, Except.mapError]
  · have positive : 0 < index.toNat := by
      have nonzero : index.toNat ≠ 0 := by
        intro equal
        apply zero
        apply UInt64.toNat_inj.mp
        simpa using equal
      omega
    have division : stride.bytes * index / index = stride.bytes := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div, product, Nat.mul_div_cancel _ positive]
    simp only [Size.mul, division, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rw [exactProduct]
    rfl

theorem array_formula_runtime_value_nat (stride : Size) (count : UInt64) (index : Nat)
    (endpoint : count.toNat = 0 ∨ stride.bytes.toNat * (count.toNat - 1) < 2^64)
    (inside : index < count.toNat) :
    (FieldsShape.Array stride count).offset index =
      .ok (Size.ofBytes (UInt64.ofNat (stride.bytes.toNat * index))) := by
  have fits : index < 2^64 := Nat.lt_trans inside count.toNat_lt
  have exactIndex : (UInt64.ofNat index).toNat = index := UInt64.toNat_ofNat_of_lt' fits
  simpa only [exactIndex] using array_formula_runtime_value stride count (UInt64.ofNat index)
    endpoint (by simpa only [exactIndex] using inside)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def shape (stride count : Nat) : FieldShape :=
  ⟨.array, count, none, some stride, #[], #[]⟩

private def layoutText (stride count : Nat) (offsets : String) : String :=
  "{\"size_bytes\":" ++ toString (stride * count) ++
  ",\"abi_align_bytes\":1,\"unadjusted_abi_align_bytes\":1,\"max_repr_align_bytes\":null," ++
  "\"repr_c\":false,\"uninhabited\":false,\"largest_niche\":null,\"randomization_seed\":0," ++
  "\"fields\":{\"kind\":\"array\",\"stride_bytes\":" ++ toString stride ++
  ",\"field_count\":" ++ toString count ++ "},\"field_offsets_bytes\":" ++ offsets ++
  ",\"variants\":{\"kind\":\"single\",\"variant_index\":0},\"backend_repr\":{\"kind\":\"memory\",\"sized\":true}}"

private def formula (stride count : Nat) : String :=
  "{\"kind\":\"array\",\"stride_bytes\":" ++ toString stride ++ ",\"field_count\":" ++ toString count ++ "}"

private def parse (stride count : Nat) (offsets : String) :=
  JsonReader.run DecoderValues.parseLayout (layoutText stride count offsets)

def main : IO Unit := do
  for (stride,count) in [(1,2^50), (4,2^48), (0,2^64-1), (8,0), (8,1)] do
    let .ok source := parse stride count (formula stride count) | throw (IO.userError "valid formula rejected")
    let .ok runtime := RuntimeMetadata.layout RuntimeTargetDataLayout.default source
      | throw (IO.userError "valid formula did not lower")
    check (runtime.fields.count == count) "compact count lost"
    if count > 0 then
      for index in [0,count/2,count-1] do
        check ((runtime.fields.offset index).toOption.map (·.bytes.toNat) == some (stride*index)) "offset differs"
    check (!(runtime.fields.offset count).isOk) "out-of-bounds field accepted"
  for (stride,count,bad) in [(2,3,formula 3 3), (2,3,formula 2 4),
      (2^63,3,formula (2^63) 3), (0,2^64,formula 0 (2^64)), (2^64,0,formula (2^64) 0),
      (2,3,"{\"kind\":\"unknown\",\"stride_bytes\":2,\"field_count\":3}"),
      (2,3,"{\"kind\":\"array\",\"stride_bytes\":2}"), (2,3,"[0,2]")] do
    check (!(parse stride count bad).isOk) "malformed formula accepted"
  let wrongShape := (LayoutFieldOffsets.arrayFormula 0 0).validate ⟨.primitive,0,none,none,#[],#[]⟩
  check (!wrongShape.isOk) "formula accepted for non-array shape"
  let .ok legacy := parse 2 3 "[0,2,4]" | throw (IO.userError "legacy explicit array rejected")
  check (RuntimeMetadata.layout RuntimeTargetDataLayout.default legacy).isOk "legacy lowering rejected"
  let .ok badLegacy := parse 2 3 "[0,2,5]" | throw (IO.userError "legacy count check moved")
  check (!(RuntimeMetadata.layout RuntimeTargetDataLayout.default badLegacy).isOk) "legacy bad offset accepted"
  IO.println "PASS compact array offsets: all-index bounds theorem, huge/zero arrays, strict legacy and negative controls"
