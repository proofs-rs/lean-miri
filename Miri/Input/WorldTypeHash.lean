import Miri.Input.TypeArenaWorld
import Miri.Input.StableSipHash

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd
`TyCtxt::type_id_hash`, `StableHash` for TyKind and RawList. The supported
structural domain hashes constructor syntax after free-region erasure. Nominal
identity, higher-ranked binders and const evaluation remain separate source
operations. No query answer is retained in the execution World. -/
namespace Miri.Input.WorldTypeHash
open TypeArena

def littleEndian (width value : Nat) : ByteArray :=
  ⟨(Array.range width).map (fun index => UInt8.ofNat (value / 2^(8*index)))⟩
private def tag (value : Nat) : ByteArray := littleEndian 1 value
private def integerTag : MIR.IntegerKind → Nat
  | .isize | .usize => 0 | .i8 | .u8 => 1 | .i16 | .u16 => 2
  | .i32 | .u32 => 3 | .i64 | .u64 => 4 | .i128 | .u128 => 5
private def mutabilityTag : MIR.Mutability → Nat
  | .Not => 0 | .Mut => 1

/-- Missing structural support is distinct from malformed source identity.
An unsupported child never substitutes its final TypeId hash for raw syntax. -/
def sourceBytes (world : World) : Nat → TypeId → Except String (Option ByteArray)
  | 0, _ => throw "type hash source traversal exhausted"
  | fuel + 1, id => do
    let constructor ← match ← world.lookupType id with
      | .constructed value => pure (some value)
      | .material node => world.materialKey node
    let some constructor := constructor | return none
    match constructor with
    | .bool => pure (some (tag 0))
    | .char => pure (some (tag 1))
    | .integer signed kind =>
      unless signed == kind.signed do throw "type hash integer source signedness mismatch"
      pure (some (tag (if signed then 2 else 3) ++ tag (integerTag kind)))
    | .float kind =>
      let ordinal ← match kind with
        | .f16 => pure 0 | .f32 => pure 1 | .f64 => pure 2 | .f128 => pure 3
        | .f16b | .ppcf128 => return none
      pure (some (tag 4 ++ tag ordinal))
    | .str => pure (some (tag 7))
    | .never => pure (some (tag 21))
    | .slice child =>
      let some child ← sourceBytes world fuel child | return none
      pure (some (tag 10 ++ child))
    | .rawPointer child mutability =>
      let some child ← sourceBytes world fuel child | return none
      pure (some (tag 11 ++ child ++ tag (mutabilityTag mutability)))
    | .reference child mutability region =>
      if let .Bound .. := region then return none
      let some child ← sourceBytes world fuel child | return none
      -- RegionKind::ReErased is ordinal6; a bound region is never erased.
      pure (some (tag 12 ++ tag 6 ++ child ++ tag (mutabilityTag mutability)))
    | .tuple children =>
      let mut bytes := littleEndian 8 children.size
      for child in children do
        let some child ← sourceBytes world fuel child | return none
        bytes := bytes ++ child
      let fingerprint := StableSipHash.hash bytes
      pure (some (tag 22 ++ littleEndian 16 fingerprint.toNat))
    | _ => pure none

/-- Covered syntax is hashed on demand, including IDs outside the material
prefix. Unported material constructors retain an explicit compiler boundary. -/
def query (world : World) (fuel : Nat) (id : TypeId) : Except String Miri.ABI.U128 := do
  if let some bytes ← sourceBytes world fuel id then return StableSipHash.hash bytes
  let .material node ← world.lookupType id
    | throw "constructed type hash requires additional raw source material"
  let some facts := node.compilerFacts | throw "residual compiler TypeId hash material absent"
  let some value := facts.typeIdHash | throw "residual compiler TypeId hash material absent"
  unless value < 2^128 do throw "residual compiler TypeId hash exceeds u128"
  pure (BitVec.ofNat 128 value)
end Miri.Input.WorldTypeHash
