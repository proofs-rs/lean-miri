import Miri.Input.Model.Types

/-! Pinned rustc_middle/ty/sty.rs::discriminant_ty and CoroutineArgsExt::discr_ty;
rustc_abi::ReprOptions::discr_type. Enum representation determines the public
discriminant type, independently of any smaller physical layout tag. -/
namespace Miri.Input.StructuralDiscriminantType

def fixedBits : Miri.MIR.IntegerKind → Option Nat
  | .i8 | .u8 => some 8 | .i16 | .u16 => some 16
  | .i32 | .u32 => some 32 | .i64 | .u64 => some 64
  | .i128 | .u128 => some 128 | .isize | .usize => none

def enumKey (representation : ReprOptions) : Except String String := do
  match representation.integer with
  | none => pure "isize"
  | some (.pointerSized signed) => pure (if signed then "isize" else "usize")
  | some (.fixed (.known kind) bits signed) =>
    unless fixedBits kind == some bits do throw "enum discriminant repr integer width mismatch"
    pure ((if signed then "i" else "u") ++ toString bits)

structure Hooks where
  shape : TypeId → Except String TypeShape
  primitive : String → Except String TypeId
  normalizeAlias : Nat → TypeId → Except String TypeId
  eraseUnsafeBinder : TypeId → Except String TypeId

def query (hooks : Hooks) : Nat → TypeId → Except String TypeId
  | 0, _ => .error "discriminant type traversal exhausted"
  | fuel + 1, id => do
    match ← hooks.shape id with
    | .adt data =>
      let key ← if data.kind == .enumKind then enumKey data.representation else pure "u8"
      hooks.primitive key
    | .coroutine .. => hooks.primitive "u32"
    | .patternType inner _ => query hooks fuel inner
    | .unsafeBinder .. => query hooks fuel (← hooks.eraseUnsafeBinder id)
    | .alias .. =>
      let normalized ← hooks.normalizeAlias fuel id
      if normalized == id then throw "discriminant type alias remained unresolved"
      query hooks fuel normalized
    | _ => hooks.primitive "u8"

end Miri.Input.StructuralDiscriminantType
