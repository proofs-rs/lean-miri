import Miri.Input.TypeArenaWorld
import Miri.Input.StableSipHash
import Miri.Input.DefinitionPathHash
import Miri.Input.AdtStableHash

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd
`TyCtxt::type_id_hash`, `StableHash` for TyKind and RawList. The supported
structural domain hashes constructor syntax after free-region erasure. Nominal
types use reconstructed DefKeys and raw ADT declarations. Value constants
retain their declared types and ValTree syntax; higher-ranked binders and
unevaluated constants retain an explicit residual boundary. No query answer
is retained in the execution World. -/
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

private def definitionBytes (world : World) (identity : GenericSubstitution.DefinitionIdentity) :
    Except String ByteArray := do
  let reference ← world.definitionRef identity
  let some source := world.definitions[reference]? | throw "type hash physical definition is absent"
  let some path := source.rawPath | throw "type hash raw definition path is absent"
  pure (littleEndian 16 (← DefinitionPathHash.query path).toNat)

mutual
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
    | .adt identity arguments | .functionDefinition identity arguments _ =>
      let reference ← world.definitionRef identity
      let some source := world.definitions[reference]? | throw "type hash nominal definition is absent"
      let some template := source.genericTemplate | throw "type hash nominal declaration template is absent"
      unless template.parameters.size == arguments.size do
        throw "type hash nominal argument domain differs from its declaration"
      for (sort,argument) in template.parameters.zip arguments do
        let compatible := match sort,argument with
          | .type,.Type _ | .region,.Lifetime _ | .constant,.Const _ => true
          | _,_ => false
        unless compatible do throw "type hash nominal argument sort differs from its declaration"
      let mut argumentBytes := littleEndian 8 arguments.size
      for argument in arguments do
        match argument with
        | .Type child =>
          let some child ← sourceBytes world fuel child | return none
          argumentBytes := argumentBytes ++ tag 1 ++ child
        | .Lifetime region =>
          if let .Bound .. := region then return none
          argumentBytes := argumentBytes ++ tag 0 ++ tag 6
        | .Const child =>
          let some child ← constantBytes world fuel child | return none
          argumentBytes := argumentBytes ++ tag 2 ++ child
      let argumentsHash := littleEndian 16 (StableSipHash.hash argumentBytes).toNat
      match constructor with
      | .adt .. =>
        let some declaration := source.adtDeclaration | throw "type hash ADT declaration is absent"
        declaration.validate template
        let declarationHash ← AdtStableHash.query (definitionBytes world) identity declaration
        pure (some (tag 5 ++ littleEndian 16 declarationHash.toNat ++ argumentsHash))
      | .functionDefinition _ _ variables =>
        unless variables.isEmpty do return none
        -- FnDef carries Binder<GenericArgs>; even an empty bound-variable
        -- RawList contributes its independently hashed length prefix.
        let variablesHash := StableSipHash.hash (littleEndian 8 0)
        pure (some (tag 13 ++ (← definitionBytes world identity) ++ argumentsHash ++
          littleEndian 16 variablesHash.toNat))
      | _ => throw "type hash nominal source constructor changed"
    | .str => pure (some (tag 7))
    | .foreign identity => pure (some (tag 6 ++ (← definitionBytes world identity)))
    | .never => pure (some (tag 21))
    | .array child length =>
      let some child ← sourceBytes world fuel child | return none
      let some length ← constantBytes world fuel length | return none
      pure (some (tag 8 ++ child ++ length))
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

/-- ConstKind::Value hashes its declared type and the raw ValTree constructor.
Branch children are constant IDs, and RawList contributes its own fingerprint. -/
def constantBytes (world : World) : Nat → TypeConstantId → Except String (Option ByteArray)
  | 0, _ => throw "type hash constant traversal exhausted"
  | fuel + 1, id => do
    let source ← world.lookupConstant id
    let .Value ty tree := source | return none
    let some ty ← sourceBytes world fuel ty | return none
    unless tree.root == 0 && tree.nodes.size == 1 do
      throw "type hash value tree is not a canonical raw source node"
    let some root := tree.nodes[tree.root]? | throw "type hash value tree root is absent"
    let value ← match root with
      | .Leaf bits size =>
        unless size > 0 && size ≤ 16 && bits < 2^(8*size) do
          throw "type hash scalar value exceeds its source width"
        pure (tag 0 ++ littleEndian 16 bits ++ tag size)
      | .Branch children =>
        let mut bytes := littleEndian 8 children.size
        for child in children do
          let some child ← constantBytes world fuel child | return none
          bytes := bytes ++ child
        pure (tag 1 ++ littleEndian 16 (StableSipHash.hash bytes).toNat)
    pure (some (tag 5 ++ ty ++ value))
end

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
