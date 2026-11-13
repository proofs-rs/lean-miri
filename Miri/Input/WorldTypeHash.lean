import Miri.Input.TypeArenaWorld
import Miri.Input.StableSipHash
import Miri.Input.DefinitionPathHash
import Miri.Input.AdtStableHash
import Miri.Input.GenericInstantiationWorld
import Miri.Input.BinderRegions
import Miri.Input.FunctionPointerStableHash
import Miri.Input.DynamicStableHash

/-! Pinned rustc 8144389c895da997dbdecaa635e41d6a50be6ffd
`TyCtxt::type_id_hash`, `StableHash` for TyKind and RawList. The supported
structural domain hashes constructor syntax after free-region erasure. Nominal
types use reconstructed DefKeys and raw ADT declarations. Value constants
retain their declared types and ValTree syntax. Function-pointer headers and
region binders and escaping bound regions are hashed from raw syntax.
Unevaluated constants and non-region binders retain an explicit residual boundary. No
query answer is retained in the execution World. -/
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

private def regionBytes (world : World) (region : MIR.Region) : Except String (Option ByteArray) := do
  match region with
  | .Bound indexKind variableIndex kind =>
    unless variableIndex < 2^32 do throw "bound region variable exceeds u32"
    let index ← match indexKind with
      | .Bound depth =>
        unless depth < 2^32 do throw "bound region depth exceeds u32"
        pure (tag 0 ++ littleEndian 4 depth)
      | .Canonical => pure (tag 1)
    let kind ← match kind with
      | .Anon => pure (tag 0)
      | .NamedForPrinting name => pure (tag 1 ++ littleEndian 8 name.toUTF8.size ++ name.toUTF8)
      | .Named reference => pure (tag 2 ++ (← definitionBytes world (← world.identity reference)))
      | .ClosureEnv => pure (tag 3)
    pure (some (tag 1 ++ index ++ littleEndian 4 variableIndex ++ kind))
  | _ => pure (some (tag 6))

private def sourceConstructor (world : World) (id : TypeId) : Except String Constructor := do
  match ← world.lookupType id with
  | .constructed key => pure key
  | .material node =>
    let some key ← world.materialKey node | throw "closure hash child source constructor is unavailable"
    pure key

/-- Pinned ClosureArgs consists of the parent prefix and three synthetic type
arguments: closure kind, RustCall signature, and tupled captures. No callable
body or result hash supplies their identity. -/
private def validateClosureHeader (world : World)
    (identity : GenericSubstitution.DefinitionIdentity) (arguments : Array MIR.GenericArg) : Except String Unit := do
  let reference ← world.definitionRef identity
  let some definition := world.definitions[reference]? | throw "closure hash physical owner absent"
  let some path := definition.rawPath | throw "closure hash raw definition path absent"
  unless path.components.back?.any (·.kind == "closure") do throw "closure hash owner is not a raw closure definition"
  let header ← DefinitionPath.requireGenerics path
  unless header.parameters.size == arguments.size && header.parentParameterCount + 3 == arguments.size do
    throw "closure hash raw generic/synthetic argument domain mismatch"
  for (sort,argument) in header.parameters.zip arguments do
    unless (match sort,argument with
      | .type,.Type _ | .region,.Lifetime _ | .constant,.Const _ => true | _,_ => false) do
      throw "closure hash generic argument sort mismatch"
  let some (.Type kind) := arguments[header.parentParameterCount]? | throw "closure hash kind type absent"
  let .integer true width ← sourceConstructor world kind | throw "closure hash kind is not a pinned integer marker"
  unless [MIR.IntegerKind.i8,.i16,.i32].contains width do throw "closure hash kind integer marker is invalid"
  let some (.Type signature) := arguments[header.parentParameterCount + 1]? | throw "closure hash signature type absent"
  let .functionPointer signature ← sourceConstructor world signature | throw "closure hash signature source is not a FnPtr"
  let abi ← Miri.ABI.ExternAbi.ofPacked signature.abiPacked
  unless abi == .RustCall && signature.safe && !signature.cVariadic && signature.inputs.size == 1 do
    throw "closure hash signature header is outside the pinned RustCall domain"
  let some input := signature.inputs[0]? | throw "closure hash tupled signature input absent"
  unless (match ← sourceConstructor world input with | .tuple .. => true | _ => false) do
    throw "closure hash signature input is not tupled"
  let some (.Type captures) := arguments[header.parentParameterCount + 2]? | throw "closure hash capture type absent"
  unless (match ← sourceConstructor world captures with | .tuple .. => true | _ => false) do
    throw "closure hash capture source is not a tuple"

mutual
/-- Missing structural support is distinct from malformed source identity.
An unsupported child never substitutes its final TypeId hash for raw syntax. -/
private def rawSourceBytes (world : World) (normalized : Bool) : Nat → TypeId → Except String (Option ByteArray)
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
          let some child ← rawSourceBytes world normalized fuel child | return none
          argumentBytes := argumentBytes ++ tag 1 ++ child
        | .Lifetime region =>
          let some bytes ← regionBytes world region | return none
          argumentBytes := argumentBytes ++ tag 0 ++ bytes
        | .Const child =>
          let some child ← constantBytes world normalized fuel child | return none
          argumentBytes := argumentBytes ++ tag 2 ++ child
      let argumentsHash := littleEndian 16 (StableSipHash.hash argumentBytes).toNat
      match constructor with
      | .adt .. =>
        let some declaration := source.adtDeclaration | throw "type hash ADT declaration is absent"
        declaration.validate template
        let declarationHash ← AdtStableHash.query (definitionBytes world) identity declaration
        pure (some (tag 5 ++ littleEndian 16 declarationHash.toNat ++ argumentsHash))
      | .functionDefinition _ _ variables =>
        unless normalized || variables.isEmpty do return none
        let mut variableBytes := littleEndian 8 variables.size
        for boundVariable in variables do
          match boundVariable with
          | .Region .Anon => variableBytes := variableBytes ++ tag 1 ++ tag 0
          | _ => return none
        let variablesHash := StableSipHash.hash variableBytes
        pure (some (tag 13 ++ (← definitionBytes world identity) ++ argumentsHash ++
          littleEndian 16 variablesHash.toNat))
      | _ => throw "type hash nominal source constructor changed"
    | .closure identity arguments =>
      validateClosureHeader world identity arguments
      let mut bytes := littleEndian 8 arguments.size
      for argument in arguments do
        match argument with
        | .Type child =>
          let some child ← rawSourceBytes world normalized fuel child | return none
          bytes := bytes ++ tag 1 ++ child
        | .Lifetime region =>
          let some child ← regionBytes world region | return none
          bytes := bytes ++ tag 0 ++ child
        | .Const child =>
          let some child ← constantBytes world normalized fuel child | return none
          bytes := bytes ++ tag 2 ++ child
      pure (some (tag 17 ++ (← definitionBytes world identity) ++
        littleEndian 16 (StableSipHash.hash bytes).toNat))
    | .functionPointer signature =>
      unless normalized || signature.variables.isEmpty do return none
      let mut bytes := littleEndian 8 (signature.inputs.size + 1)
      for child in signature.inputs.push signature.output do
        let some child ← rawSourceBytes world normalized fuel child | return none
        bytes := bytes ++ child
      let types := StableSipHash.hash bytes
      let mut variables := littleEndian 8 signature.variables.size
      for boundVariable in signature.variables do
        match boundVariable with
        | .region .anonymous => variables := variables ++ tag 1 ++ tag 0
        | _ => return none
      let variablesHash := StableSipHash.hash variables
      let header ← FunctionPointerStableHash.header signature.abiPacked signature.safe
        signature.cVariadic signature.splatted signature.inputs.size
      pure (some (tag 14 ++ littleEndian 16 types.toNat ++ littleEndian 16 variablesHash.toNat ++ header))
    | .dynamic value =>
      unless normalized do return none
      DynamicStableHash.sourceBytes (definitionBytes world)
        (rawSourceBytes world normalized fuel) (constantBytes world normalized fuel)
        (fun region => do
          let some bytes ← regionBytes world region | throw "dynamic region hash source is unsupported"
          pure bytes) value
    | .patternType base pattern =>
      let some base ← rawSourceBytes world normalized fuel base | return none
      let some pattern ← patternBytes world normalized fuel pattern | return none
      pure (some (tag 9 ++ base ++ pattern))
    | .str => pure (some (tag 7))
    | .foreign identity => pure (some (tag 6 ++ (← definitionBytes world identity)))
    | .never => pure (some (tag 21))
    | .array child length =>
      let some child ← rawSourceBytes world normalized fuel child | return none
      let some length ← constantBytes world normalized fuel length | return none
      pure (some (tag 8 ++ child ++ length))
    | .slice child =>
      let some child ← rawSourceBytes world normalized fuel child | return none
      pure (some (tag 10 ++ child))
    | .rawPointer child mutability =>
      let some child ← rawSourceBytes world normalized fuel child | return none
      pure (some (tag 11 ++ child ++ tag (mutabilityTag mutability)))
    | .reference child mutability region =>
      let some region ← regionBytes world region | return none
      let some child ← rawSourceBytes world normalized fuel child | return none
      pure (some (tag 12 ++ region ++ child ++ tag (mutabilityTag mutability)))
    | .tuple children =>
      let mut bytes := littleEndian 8 children.size
      for child in children do
        let some child ← rawSourceBytes world normalized fuel child | return none
        bytes := bytes ++ child
      let fingerprint := StableSipHash.hash bytes
      pure (some (tag 22 ++ littleEndian 16 fingerprint.toNat))
    | _ => pure none

private def patternBytes (world : World) (normalized : Bool) : Nat → CompilerPattern → Except String (Option ByteArray)
  | 0,_ => throw "type hash pattern traversal exhausted"
  | _ + 1,.notNull => pure (some (tag 2))
  | fuel + 1,.range start finish => do
    let some start ← constantBytes world normalized fuel start | return none
    let some finish ← constantBytes world normalized fuel finish | return none
    pure (some (tag 0 ++ start ++ finish))
  | fuel + 1,.or patterns => do
    unless !patterns.isEmpty do throw "pattern Or source is empty"
    let mut bytes := littleEndian 8 patterns.size
    for pattern in patterns do
      let some pattern ← patternBytes world normalized fuel pattern | return none
      bytes := bytes ++ pattern
    pure (some (tag 1 ++ littleEndian 16 (StableSipHash.hash bytes).toNat))

/-- ConstKind::Value hashes its declared type and the raw ValTree constructor.
Branch children are constant IDs, and RawList contributes its own fingerprint. -/
private def constantBytes (world : World) (normalized : Bool) : Nat → TypeConstantId → Except String (Option ByteArray)
  | 0, _ => throw "type hash constant traversal exhausted"
  | fuel + 1, id => do
    let source ← world.lookupConstant id
    let .Value ty tree := source | return none
    let some ty ← rawSourceBytes world normalized fuel ty | return none
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
          let some child ← constantBytes world normalized fuel child | return none
          bytes := bytes ++ child
        pure (tag 1 ++ littleEndian 16 (StableSipHash.hash bytes).toNat)
    pure (some (tag 5 ++ ty ++ value))
end

mutual
private def normalizationDomain (world : World) : Nat → TypeId → Except String (Bool × Bool)
  | 0,_ => throw "hash normalization domain traversal exhausted"
  | fuel + 1,id => do
    let constructor ← match ← world.lookupType id with
      | .constructed value => pure (some value)
      | .material source => world.materialKey source
    let some constructor := constructor | return (false,false)
    let own ← match constructor with
      | .bool | .char | .str | .never | .integer .. | .foreign .. => pure (true,false)
      | .float kind => pure (kind != .f16b && kind != .ppcf128,false)
      | .rawPointer .. | .reference .. | .slice .. | .tuple .. | .array .. | .adt .. | .patternType .. | .closure .. => pure (true,false)
      | .dynamic value => pure (value.predicates.all (fun predicate => BinderRegions.regionOnly predicate.variables),true)
      | .functionPointer signature => pure (BinderRegions.regionOnly signature.variables,true)
      | .functionDefinition _ _ variables =>
        pure (variables.all (fun value => match value with | .Region _ => true | _ => false),!variables.isEmpty)
      | _ => pure (false,false)
    if !own.1 then return own
    let mut needed := own.2
    for child in constructor.typeChildren do
      let (supported,required) ← normalizationDomain world fuel child
      if !supported then return (false,false)
      needed := needed || required
    for child in constructor.constantChildren do
      let (supported,required) ← constantNormalizationDomain world fuel child
      if !supported then return (false,false)
      needed := needed || required
    pure (true,needed)
private def constantNormalizationDomain (world : World) : Nat → TypeConstantId → Except String (Bool × Bool)
  | 0,_ => throw "hash constant normalization domain traversal exhausted"
  | fuel + 1,id => do
    let .Value ty tree ← world.lookupConstant id | return (false,false)
    let (supported,needed) ← normalizationDomain world fuel ty
    if !supported then return (false,false)
    unless tree.root == 0 && tree.nodes.size == 1 do throw "noncanonical value tree source"
    let some root := tree.nodes[tree.root]? | throw "value tree root absent"
    let .Branch children := root | return (true,needed)
    let mut needed := needed
    for child in children do
      let (supported,required) ← constantNormalizationDomain world fuel child
      if !supported then return (false,false)
      needed := needed || required
    pure (true,needed)
end

/-- Covered non-binder syntax hashes directly. Region binders are anonymized
on the complete root in a query-local World; no normalized result is retained. -/
def sourceBytes (world : World) (fuel : Nat) (id : TypeId) : Except String (Option ByteArray) := do
  if let some bytes ← rawSourceBytes world false fuel id then return some bytes
  let (supported,needed) ← normalizationDomain world fuel id
  unless supported && needed do return none
  let term ← GenericInstantiationWorld.ofType world fuel id
  let term ← BinderRegions.eraseAndAnonymizeOpen fuel term
  let (id,world) ← (GenericInstantiationWorld.resolveType fuel term).run world
  rawSourceBytes world true fuel id

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
/-- Raw PatternKind stream, using source endpoint constants rather than TypeId answers. -/
def patternSourceBytes (world : World) (fuel : Nat) (pattern : CompilerPattern) :
    Except String (Option ByteArray) :=
  patternBytes world false fuel pattern
end Miri.Input.WorldTypeHash
