import Miri.Input.SourceCompilerWorld
import Miri.Input.RuntimeMetadata

/-! Canonical physical pools owned by the shared evaluation World. Constructors
receive source-derived shapes/rows; they assign handles, preserve existing pools,
and reject a repeated structural key with a different full physical layout.
This module contains no compiler process, source JSON, or independent cache. -/
namespace Miri.Input.SourceCompilerWorld

/-- Raw source definitions acquire a local reference only when demanded. -/
def internDefinition (world : World) (raw : DefinitionId) : Except String (World × Nat) := do
  unless raw.crateIndex < 2^32 && raw.index < 2^32 do throw "physical source DefId exceeds rustc width"
  if let some id := world.canonical.definitions.findIdx? (· == raw) then return (world,id)
  let id := world.canonical.definitions.size
  return ({world with canonical := {world.canonical with definitions := world.canonical.definitions.push raw}},id)

private def typePresent (world : World) (id : Nat) : Except String Unit := do
  let some node := world.canonical.types[id]? | throw "physical child type handle absent"
  unless node.id == id do throw "physical child type handle/index mismatch"
private def definitionPresent (world : World) (id : Nat) : Except String Unit := do
  unless id < world.canonical.definitions.size do throw "physical source definition reference absent"
private def argumentsPresent (world : World) (args : Array MIR.GenericArg) : Except String Unit := do
  for arg in args do
    match arg with
    | .Type id => typePresent world id
    | .Const id => unless id < world.canonical.typeConstants.size do throw "physical const handle absent"
    | .Lifetime _ => pure ()

private def shapePresent (world : World) (shape : TypeShape) : Except String Unit := do
  match shape with
  | .bool | .char | .int _ | .uint _ | .float _ | .str | .never => pure ()
  | .tuple elements => for id in elements do typePresent world id
  | .rawPointer id _ | .reference id _ _ | .patternType id .notNull => typePresent world id
  | .patternType id (.range lower upper) =>
    typePresent world id
    unless lower < world.canonical.typeConstants.size && upper < world.canonical.typeConstants.size do
      throw "physical pattern range constant identity absent"
  | .array id length constructor =>
    typePresent world id
    unless length < world.canonical.typeConstants.size && constructor.canonicalValueConstructor do
      throw "physical array constant identity absent"
  | .functionDefinition definition args signature bound =>
    definitionPresent world definition
    argumentsPresent world args
    for id in signature.inputs do typePresent world id
    typePresent world signature.output
    for entry in bound do
      match entry with
      | .Region (.Named id) => definitionPresent world id
      | .Region _ => pure ()
      | _ => throw "physical function-item non-region binder unsupported"
  | .functionPointer signature bound =>
    for entry in bound do
      match entry with
      | .Region (.Named id) => definitionPresent world id
      | .Region _ => pure ()
      | _ => throw "physical function-pointer non-region binder unsupported"
    for id in signature.inputs do typePresent world id
    typePresent world signature.output
  | .adt data =>
    definitionPresent world data.definition
    argumentsPresent world data.args
    for variant in data.variants do
      for field in variant.fields do typePresent world field.typeId
  | .closure definition args _ =>
    definitionPresent world definition
    argumentsPresent world args
  | .dynamicTraitObject predicates principal _ =>
    for id in predicates do
      unless id < world.canonical.predicates.size do throw "physical dynamic predicate absent"
    if let some id := principal then
      unless predicates.contains id do throw "physical principal predicate not in object"
  | _ => throw "unsupported shared physical type shape"

private def sameIdentity : TypeShape → TypeShape → Bool
  | .bool,.bool | .char,.char | .str,.str | .never,.never => true
  | .int a,.int b | .uint a,.uint b => a == b
  | .float a,.float b => a == b
  | .rawPointer a am,.rawPointer b bm => a == b && am == bm
  | .reference a am ar,.reference b bm br => a == b && am == bm && ar == br
  | .tuple a,.tuple b => a == b
  | .patternType a .notNull,.patternType b .notNull => a == b
  | .patternType a (.range al au),.patternType b (.range bl bu) => a == b && al == bl && au == bu
  | .array a al _,.array b bl _ => a == b && al == bl
  | .adt a,.adt b => a.definition == b.definition && a.args == b.args
  | .closure a args _,.closure b args' _ => a == b && args == args'
  | .functionDefinition a args _ _,.functionDefinition b args' _ _ => a == b && args == args'
  | .functionPointer a av,.functionPointer b bv =>
    a.inputs == b.inputs && a.output == b.output && a.safety == b.safety &&
      a.abi == b.abi && a.cVariadic == b.cVariadic && av == bv
  | .dynamicTraitObject a ap ar,.dynamicTraitObject b bp br => a == b && ap == bp && ar == br
  | _,_ => false
private def sameMetadata (a b : TypeShape) : Bool :=
  sameIdentity a b && match a,b with
    | .functionDefinition _ _ a av,.functionDefinition _ _ b bv =>
      a.inputs == b.inputs && a.output == b.output && a.safety == b.safety &&
      a.abi == b.abi && a.cVariadic == b.cVariadic && av == bv
    | .adt a,.adt b => a.kind == b.kind && a.representation == b.representation && a.variants == b.variants
    | .array _ _ a,.array _ _ b => a.count == b.count && a.canonicalValueConstructor == b.canonicalValueConstructor
    | .closure _ _ a,.closure _ _ b => a == b
    | _,_ => true

/-- Canonicalize complete source-derived type identity, never identity by equal
size/alignment alone. Existing facts are retained; new rows assert no compiler
facts beyond the supplied physical source construction. -/
def internType (world : World) (shape : TypeShape) (layout : Layout) (display : String) :
    Except String (World × TypeId) := do
  shapePresent world shape
  LocalValidation.validateLayout layout "$.source_type_layout"
  let runtime ← (RuntimeMetadata.ofDocument world.canonical).mapError toString
  let computed ← (RuntimeMetadata.layout runtime.target layout).mapError toString
  let matching := world.canonical.types.filter (fun node => sameIdentity node.shape shape)
  unless matching.size ≤ 1 do throw "duplicate canonical physical type identity"
  if let some node := matching[0]? then
    unless sameMetadata node.shape shape do throw "canonical physical type metadata contradiction"
    let existing ← (runtime.lookup node.id).mapError toString
    unless existing.layout == computed do throw "canonical physical type layout contradiction"
    return (world,node.id)
  let id := world.canonical.types.size
  let layoutId := world.canonical.layouts.size
  let node : TypeNode := {id, layoutId, shape, display}
  LocalValidation.validateType node
  return ({world with canonical := {world.canonical with
    types := world.canonical.types.push node
    layouts := world.canonical.layouts.push layout}},id)

/-- Canonical typed scalar valtree leaves, currently sufficient for source array
lengths and supported usize const arguments. No allocation value is synthesized. -/
def internScalarConstant (world : World) (typeId bits sizeBytes : Nat) :
    Except String (World × Nat) := do
  typePresent world typeId
  unless sizeBytes > 0 && bits < 2^(sizeBytes*8) do throw "physical scalar constant exceeds its width"
  let constant := MIR.TypeConst.Value typeId ⟨#[.Leaf bits sizeBytes],0⟩
  if let some id := world.canonical.typeConstants.findIdx? (· == constant) then return (world,id)
  let id := world.canonical.typeConstants.size
  return ({world with canonical := {world.canonical with
    typeConstants := world.canonical.typeConstants.push constant}},id)

/-- Predicate identities retain declaration, ordered arguments, binders and
projection result. They do not represent a solved trait obligation or vtable. -/
def internPredicate (world : World) (predicate : VtablePredicate) : Except String (World × Nat) := do
  definitionPresent world predicate.definitionId
  argumentsPresent world predicate.genericArgs
  unless predicate.boundVariables.isEmpty do throw "shared physical bound existential unsupported"
  if let some id := predicate.projectionTerm then typePresent world id
  if let some id := world.canonical.predicates.findIdx? (fun p => p.kind == predicate.kind && p.definitionId == predicate.definitionId &&
      p.genericArgs == predicate.genericArgs && p.boundVariables == predicate.boundVariables &&
      p.projectionTerm == predicate.projectionTerm) then return (world,id)
  let id := world.canonical.predicates.size
  return ({world with canonical := {world.canonical with
    predicates := world.canonical.predicates.push predicate}},id)
end Miri.Input.SourceCompilerWorld
