import Miri.Input.AdtDeclaration
import Miri.Input.StableSipHash

/-! Pinned AdtDefData stable hashing from raw declaration syntax. Definition
identities are resolved by the caller, so this operation cannot consult a
compiler hash answer or depend on the execution World's representation. -/
namespace Miri.Input.AdtStableHash
open AdtDeclaration
private def le (width value : Nat) : ByteArray :=
  ⟨(Array.range width).map (fun index => UInt8.ofNat (value / 2^(8*index)))⟩
private def byte (value : Nat) : ByteArray := le 1 value
private def symbol (value : String) : ByteArray := le 8 value.toUTF8.size ++ value.toUTF8
private def optionalDefinition (resolve : GenericSubstitution.DefinitionIdentity → Except String ByteArray)
    (value : Option GenericSubstitution.DefinitionIdentity) : Except String ByteArray := do
  match value with
  | none => pure (byte 0)
  | some identity => pure (byte 1 ++ (← resolve identity))
private def align (value : Option Nat) : Except String ByteArray := do
  match value with
  | none => pure (byte 0)
  | some value =>
    unless value > 0 && value == 2^value.log2 && value.log2 < 64 do
      throw "stable hash representation alignment is not a supported power of two"
    pure (byte 1 ++ byte value.log2)
private def representation (repr : ReprOptions) : Except String ByteArray := do
  let integer ← match repr.integer with
    | none => pure (byte 0)
    | some (.pointerSized signed) => pure (byte 1 ++ byte 0 ++ byte (if signed then 1 else 0))
    | some (.fixed (.known kind) size signed) =>
      unless kind.signed == signed do throw "stable hash representation integer signedness mismatch"
      let ordinal ← match size with
        | 8 => pure 0 | 16 => pure 1 | 32 => pure 2 | 64 => pure 3 | 128 => pure 4
        | _ => throw "stable hash representation integer width is invalid"
      unless kind != .isize && kind != .usize && (match kind with
        | .i8 | .u8 => 8 | .i16 | .u16 => 16 | .i32 | .u32 => 32
        | .i64 | .u64 => 64 | .i128 | .u128 => 128 | _ => 0) == size do
        throw "stable hash representation integer kind differs from width"
      pure (byte 1 ++ byte 1 ++ byte ordinal ++ byte (if signed then 1 else 0))
  unless repr.flagsBits < 256 && repr.fieldShuffleSeed < 2^64 do
    throw "stable hash representation flags or shuffle seed exceed source width"
  let scalable ← match repr.scalableElement with
    | none => pure (byte 0)
    | some .container => pure (byte 1 ++ byte 1)
    | some (.elementCount count) =>
      unless count < 2^16 do throw "stable hash scalable element count exceeds u16"
      pure (byte 1 ++ byte 0 ++ le 2 count)
  pure (integer ++ (← align repr.alignBytes) ++ (← align repr.packBytes) ++
    byte repr.flagsBits ++ scalable ++ le 8 repr.fieldShuffleSeed)

def query (resolve : GenericSubstitution.DefinitionIdentity → Except String ByteArray)
    (identity : GenericSubstitution.DefinitionIdentity) (material : Material) : Except String Miri.ABI.U128 := do
  material.validateRaw
  let mut bytes ← resolve identity
  bytes := bytes ++ le 8 material.variants.size
  for (variant,index) in material.variants.zipIdx do
    bytes := bytes ++ (← resolve variant.definition)
    bytes := bytes ++ (← match variant.constructor with
      | none => pure (byte 0)
      | some constructor => pure (byte 1 ++ byte (match constructor.kind with
          | .function => 0 | .constant => 1) ++ (← resolve constructor.definition)))
    bytes := bytes ++ symbol variant.name
    bytes := bytes ++ (← match variant.discriminant with
      | .explicit definition => pure (byte 0 ++ (← resolve definition))
      | .relative distance => pure (byte 1 ++ le 4 distance))
    let fields := material.fields.filter (·.variantIndex == index)
    bytes := bytes ++ le 8 fields.size
    for field in fields do
      bytes := bytes ++ (← resolve field.definition) ++ symbol field.fieldName
      bytes := bytes ++ (← match field.visibility with
        | none => pure (byte 0)
        | some definition => pure (byte 1 ++ (← resolve definition)))
      bytes := bytes ++ (← match field.mutationRestriction with
        | none => pure (byte 0)
        | some definition => pure (byte 1 ++ (← resolve definition)))
      bytes := bytes ++ byte (if field.isUnsafe then 0 else 1) ++
        (← optionalDefinition resolve field.defaultValue)
    -- Valid source declarations have no ErrorGuaranteed taint.
    bytes := bytes ++ byte 0 ++ byte variant.flagsBits
  bytes := bytes ++ le 2 material.flagsBits ++ (← representation material.representation)
  pure (StableSipHash.hash bytes)
end Miri.Input.AdtStableHash
