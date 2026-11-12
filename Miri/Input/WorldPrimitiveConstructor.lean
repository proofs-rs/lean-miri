import Miri.Input.TypeArenaWorld
import Miri.ABI.RuntimeLayout

namespace Miri.Input.WorldPrimitiveConstructor
open TypeArena Miri.ABI
private def lift [Monad m] [MonadExceptOf String m] (value : Except String α) : m α :=
  match value with | .ok result => pure result | .error error => throw error

/-- Primitive syntax creates identity in the active World. No numeric material
anchor can be borrowed from an unrelated source-prefix arena. -/
def query (target : RuntimeTargetDataLayout) (key : String) : WorldM TypeId := do
  unless (← get).pointerBytes == target.pointerSize.bytes.toNat do
    throw "primitive query target/world pointer width mismatch"
  let integer : Option (Bool × Miri.MIR.IntegerKind) := match key with
    | "u8" => some (false,.u8) | "u16" => some (false,.u16) | "u32" => some (false,.u32)
    | "u64" => some (false,.u64) | "u128" => some (false,.u128) | "usize" => some (false,.usize)
    | "i8" => some (true,.i8) | "i16" => some (true,.i16) | "i32" => some (true,.i32)
    | "i64" => some (true,.i64) | "i128" => some (true,.i128) | "isize" => some (true,.isize)
    | _ => none
  if let some (signed,kind) := integer then return ← World.internType (.integer signed kind)
  match key with
  | "bool" => World.internType .bool
  | "unit" => World.internType (.tuple #[])
  | "pointer_tag_integer" =>
    let integer ← lift (target.ptrSizedInteger |>.mapError toString)
    let kind ← match integer with
      | .I16 => pure Miri.MIR.IntegerKind.u16 | .I32 => pure .u32 | .I64 => pure .u64
      | _ => throw "unsupported target pointer tag integer width"
    World.internType (.integer false kind)
  | "unit_pointer_const" | "unit_pointer_mut" =>
    let unit ← World.internType (.tuple #[])
    World.internType (.rawPointer unit (if key == "unit_pointer_mut" then .Mut else .Not))
  | "imm_u8_pointer" | "imm_u8_pointer_pointer" =>
    let byte ← World.internType (.integer false .u8)
    let pointer ← World.internType (.rawPointer byte .Not)
    if key == "imm_u8_pointer" then pure pointer
    else World.internType (.rawPointer pointer .Not)
  | _ => throw s!"unknown compiler primitive query {key}"
end Miri.Input.WorldPrimitiveConstructor
