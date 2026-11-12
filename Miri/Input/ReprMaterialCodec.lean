import Miri.Input.ReprMaterial
import Lean.Data.Json

namespace Miri.Input.ReprMaterialCodec
open Lean

private def keys (value : Json) (allowed : List String) : Except String Unit := do
  for (key, _) in (← value.getObj?).toArray do
    unless allowed.contains key do throw s!"unknown representation attribute {key}"

private def integerTag (value : String) : Except String IntegerTypeTag := do
  let kind ← match value with
    | "i8" => pure Miri.MIR.IntegerKind.i8 | "i16" => pure .i16 | "i32" => pure .i32
    | "i64" => pure .i64 | "i128" => pure .i128 | "isize" => pure .isize
    | "u8" => pure .u8 | "u16" => pure .u16 | "u32" => pure .u32
    | "u64" => pure .u64 | "u128" => pure .u128 | "usize" => pure .usize
    | _ => throw "unknown representation integer kind"
  pure (.known kind)

private def integer (value : Json) : Except String ReprInteger := do
  let kind ← (← value.getObjVal? "kind").getStr?
  match kind with
  | "pointer_sized" =>
    keys value ["kind", "signed"]
    return .pointerSized (← (← value.getObjVal? "signed").getBool?)
  | "fixed" =>
    keys value ["kind", "signed", "integer_kind", "size_bits"]
    return .fixed (← integerTag (← (← value.getObjVal? "integer_kind").getStr?))
      (← (← value.getObjVal? "size_bits").getNat?) (← (← value.getObjVal? "signed").getBool?)
  | _ => throw "unknown representation integer constructor"

private def scalable (value : Json) : Except String ScalableElement := do
  match ← (← value.getObjVal? "kind").getStr? with
  | "element_count" =>
    keys value ["kind", "count"]
    return .elementCount (← (← value.getObjVal? "count").getNat?)
  | "container" =>
    keys value ["kind"]
    pure .container
  | _ => throw "unknown scalable representation constructor"

private def optional (read : Json → Except String α) (value : Json) : Except String (Option α) :=
  if value == .null then pure none else return some (← read value)

/-- One strict representation decoder serves raw declarations and type shapes;
missing attributes never acquire implicit repr(Rust) or session-seed defaults. -/
def read (value : Json) : Except String ReprOptions := do
  keys value ["integer", "align_bytes", "pack_bytes", "flags_bits", "scalable_element", "field_shuffle_seed"]
  let flagsBits ← (← value.getObjVal? "flags_bits").getNat?
  let fieldShuffleSeed ← (← value.getObjVal? "field_shuffle_seed").getNat?
  unless flagsBits < 256 do throw "representation flags exceed u8"
  unless fieldShuffleSeed < 2^64 do throw "representation shuffle seed exceeds u64"
  return {
    integer := ← optional integer (← value.getObjVal? "integer")
    alignBytes := ← optional Json.getNat? (← value.getObjVal? "align_bytes")
    packBytes := ← optional Json.getNat? (← value.getObjVal? "pack_bytes")
    scalableElement := ← optional scalable (← value.getObjVal? "scalable_element")
    flagsBits, fieldShuffleSeed }

end Miri.Input.ReprMaterialCodec
