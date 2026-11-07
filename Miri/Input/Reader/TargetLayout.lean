import Miri.Input.Reader.JsonFields
import Miri.Input.RuntimeMetadataError
import Miri.ABI.Layout

/-! Canonical target layout fields are decoded once while the transport catalog
is available. Runtime metadata consumes this checked typed result directly. -/
namespace Miri.Input.Reader.TargetLayout
open Lean Miri.ABI
variable [JsonFields]
abbrev Result := Except RuntimeMetadataError
private def convert (path : String) (result : Except String α) : Result α :=
  result.mapError (.invalid path)
private def jsonField (j : Json) (name : String) : Result Json :=
  convert name (Reader.jsonField? j name)
private def number (j : Json) (name : String) : Result Nat := do
  convert name ((← jsonField j name).getNat?)
private def truth (j : Json) (name : String) : Result Bool := do
  convert name ((← jsonField j name).getBool?)
private def text (j : Json) (name : String) : Result String := do
  convert name ((← jsonField j name).getStr?)
private def array (j : Json) (name : String) : Result (Array Json) := do
  convert name ((← jsonField j name).getArr?)
private def u64 (n : Nat) (path : String) : Result UInt64 :=
  if n < 2^64 then pure (UInt64.ofNat n) else throw (.invalid path "u64 overflow")
private def u32 (n : Nat) (path : String) : Result UInt32 :=
  if n < 2^32 then pure (UInt32.ofNat n) else throw (.invalid path "u32 overflow")
private def size (n : Nat) : Result Size := Size.ofBytes <$> u64 n "size"
private def alignment (n : Nat) : Result Align := do
  if n == 0 then throw (.invalid "alignment" "zero alignment")
  (Align.fromBytes (← u64 n "alignment")).mapError (fun e => .invalid "alignment" (toString e))

private def pointerSpec (j : Lean.Json) : Result PointerSpec := do
  return ⟨← size (← number j "pointer_size_bytes"),
    ← alignment (← number j "pointer_align_bytes"),
    ← size (← number j "pointer_offset_bytes"), ← truth j "is_fat"⟩

/-- Every canonical target field is required. LLVM's original layout string
and address-space bounds stay in the enclosing source document as evidence. -/
def importTarget (j : Lean.Json) : Result RuntimeTargetDataLayout := do
  if (← text j "status") != "supported" then throw (.unsupported "target layout")
  let endian ← match ← text j "endian" with
    | "little" => pure Endian.little | "big" => pure .big
    | _ => throw (.unsupported "target endian")
  let width ← match ← number j "pointer_width_bits" with
    | 16 => pure PointerWidth.w16 | 32 => pure .w32 | 64 => pure .w64
    | _ => throw (.unsupported "target pointer width")
  let base : TargetDataLayout := ⟨endian, width⟩
  if (← u64 (← number j "object_size_bound_bytes") "object bound") != base.objSizeBound then
    throw (.invalid "object bound" "target arithmetic view mismatch")
  let align (name : String) := do alignment (← number j (name ++ "_align_bytes"))
  let vectors ← (← array j "vector_align").mapM fun entry => do
    pure (← size (← number entry "size_bytes"), ← alignment (← number entry "align_bytes"))
  let spaces ← (← array j "address_space_info").mapM fun entry => do
    pure (AddressSpace.mk (← u32 (← number entry "address_space") "address space"),
      ← pointerSpec (← jsonField entry "spec"))
  let cEnum ← match ← text j "c_enum_min_size" with
    | "I8" => pure Integer.I8 | "I16" => pure .I16 | "I32" => pure .I32
    | "I64" => pure .I64 | "I128" => pure .I128
    | _ => throw (.unsupported "C enum min size")
  let result : RuntimeTargetDataLayout := {
    base, i1Align := ← align "i1", i8Align := ← align "i8", i16Align := ← align "i16",
    i32Align := ← align "i32", i64Align := ← align "i64", i128Align := ← align "i128",
    f16Align := ← align "f16", f32Align := ← align "f32", f64Align := ← align "f64",
    f128Align := ← align "f128", aggregateAlign := ← align "aggregate", vectorAlign := vectors,
    defaultAddressSpace := ⟨← u32 (← number j "default_address_space") "default address space"⟩,
    defaultAddressSpacePointerSpec := ← pointerSpec (← jsonField j "default_address_space_pointer_spec"),
    addressSpaceInfo := spaces,
    instructionAddressSpace := ⟨← u32 (← number j "instruction_address_space") "instruction address space"⟩,
    cEnumMinSize := cEnum }
  result.validate.mapError (fun e => .invalid "target" (toString e))
  return result


end Miri.Input.Reader.TargetLayout
