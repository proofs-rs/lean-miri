import Miri.Input.Model
import Miri.Input.LocalValidation
import Miri.Input.Model.SourceSymbols

/-! Persistent, evaluation-local canonical compiler identities. The source
universe is finite declarations; substitutions are interned only when demanded.
IDs below are dense local handles, never rustc allocation IDs or salt values.
The immutable input is extended persistently; no IO, process or shared cache is
used. Every consumer must read the same updated World, not a saved table view.
Identity availability is distinct from executable MIR/ABI availability. -/
namespace Miri.Input.SourceCompilerWorld
open Miri.Interpreter

abbrev ParameterKind := SourceSymbols.ParameterKind
abbrev ItemKind := SourceMaterial.ItemKind
abbrev ItemDeclaration := SourceMaterial.ItemDeclaration

/-- Raw source DefId and complete canonical generic arguments. Raw definitions
remain usable for symbolic foreign candidates before any local IDs exist. -/
structure InstanceKey where
  definition : DefinitionId
  arguments : Array MIR.GenericArg
  deriving Repr, DecidableEq

/-- A deferred generic constant occurrence retains its full caller identity.
The token indexes this table only; it is unrelated to compiler allocation IDs. -/
structure ConstantRequest where
  caller : CallInstance
  callerArguments : Array MIR.GenericArg
  definition : SourceTypes.DefinitionRef
  arguments : Array SourceTypes.Argument
  promoted : Option Nat
  types : Array (Option SourceTypes.Concrete)
  constants : Array (Option Nat)
  expectedType : TypeId
  deriving Repr

structure World where
  canonical : ImportDocument
  private keys : Array (InstanceKey × CallInstance) := #[]
  /-- Evaluation-local ABI answers derived from typed source demands. Imported
  canonical rows alone never establish this capability in source mode. -/
  derivedInstanceAbis : Array Catalog.InstanceAbi := #[]
  /-- Compiler span identity, including parent, is distinct from diagnostic coordinates. -/
  derivedSourceSpans : Array (SourceMir.SpanKey × SpanId) := #[]
  /-- Initial existing vtable keys are canonicalized once on the first demand. -/
  initialVTableIdentities : Option (Array SourceAllocationIdentity.CanonicalVTable) := none
  derivedVTableIdentities : Array SourceAllocationIdentity.CanonicalVTable := #[]
  private constantRequests : Array ConstantRequest := #[]

structure Access (S : Type) where
  get : S → Option World
  put : S → World → S

private def checkDefinition (definition : DefinitionId) : Except String Unit := do
  unless definition.crateIndex < 2^32 && definition.index < 2^32 do
    throw "source compiler DefId exceeds rustc index width"

/-- Exact canonical node lookup. No source query silently returns a default. -/
def node (world : World) (id : CallInstance) : Except String InstanceNode := do
  let some value := world.canonical.instances[id]? | throw "source compiler instance handle absent"
  unless value.id == id do throw "source compiler instance handle/index mismatch"
  return value

def keyOf (world : World) (id : CallInstance) : Except String InstanceKey := do
  let value ← node world id
  let .Item definition := value.instanceKind | throw "source Item key requested for non-Item instance"
  let some raw := world.canonical.definitions[definition]? | throw "source instance DefId reference absent"
  return ⟨raw,value.genericArgs⟩

/-- Register syntax without evaluating it. Equal requests in one caller keep
one token, independent of how many operands reference that same constant. -/
def internConstantRequest (world : World) (caller : CallInstance)
    (definition : SourceTypes.DefinitionRef) (arguments : Array SourceTypes.Argument)
    (promoted : Option Nat) (types : Array (Option SourceTypes.Concrete))
    (constants : Array (Option Nat)) (expectedType : TypeId) : Except String (World × Nat) := do
  let key ← keyOf world caller
  if let some token := world.constantRequests.findIdx? (fun row => row.caller == caller &&
      row.definition == definition && row.arguments == arguments && row.promoted == promoted &&
      row.expectedType == expectedType) then return (world,token)
  let token := world.constantRequests.size
  let row := ConstantRequest.mk caller key.arguments definition arguments promoted types constants expectedType
  return ({world with constantRequests := world.constantRequests.push row},token)

def constantRequest (world : World) (token : Nat) : Except String ConstantRequest := do
  let some row := world.constantRequests[token]? | throw "source constant request token unavailable"
  return row

/-- Seed existing canonical handles without enumerating any new substitution. -/
def create (canonical : ImportDocument) : Except String World := do
  if let some source := canonical.sourceMaterial then
    source.validate
    unless source.target.triple == canonical.producer.targetTriple do
      throw "source material target differs from canonical compilation"
    if let some sourceLayout := source.target.runtimeDataLayout then
      if let some canonicalLayout := canonical.runtimeTargetDataLayout then
        unless sourceLayout == canonicalLayout do
          throw "source material physical target differs from canonical layout pools"
  let mut seen := #[]
  for definition in canonical.definitions do
    checkDefinition definition
    unless !seen.contains definition do throw "duplicate canonical source DefId"
    seen := seen.push definition
  let mut world : World := {canonical}
  for i in [:canonical.instances.size] do
    let value ← node world i
    LocalValidation.validateInstance value
    if let .Item _ := value.instanceKind then
      let key ← keyOf world i
      unless !(world.keys.any fun pair => pair.1 == key) do
        throw "duplicate canonical source Item key"
      world := {world with keys := world.keys.push (key,i)}
  return world

def findItem (world : World) (key : InstanceKey) : Option CallInstance :=
  (world.keys.find? fun entry => entry.1 == key).map (·.2)

private def checkArguments (world : World) (parameters : Array ParameterKind)
    (arguments : Array MIR.GenericArg) : Except String Unit := do
  unless parameters.size == arguments.size do throw "source Item generic argument count mismatch"
  for (parameter,argument) in parameters.zip arguments do
    match parameter,argument with
    | .region, .Lifetime _ => pure ()
    | .typeParameter, .Type id =>
      let some value := world.canonical.types[id]? | throw "source Item type argument absent"
      unless value.id == id do throw "source Item type handle/index mismatch"
    | .constParameter, .Const id =>
      unless id < world.canonical.typeConstants.size do throw "source Item const argument absent"
    | _,_ => throw "source Item generic argument kind mismatch"

/-- A retained typed source universe is authoritative. Headers from another
catalog cannot assign a contradictory canonical identity in this World. -/
def validateItemSource (declarations : Array ItemDeclaration) (world : World) (key : InstanceKey) :
    Except String Unit := do
  if let some source := world.canonical.sourceMaterial then
    let supplied := declarations.filter (·.definition == key.definition)
    let retained := source.declarations.filter (·.definition == key.definition)
    unless supplied.size == 1 && retained.size == 1 && supplied[0]? == retained[0]? do
      throw "Item declaration differs from retained typed source material"

/-- Construct `Instance::new_raw(Item, args)` on demand. This is not trait
resolution and does not establish MIR, ABI, promoted, inline or symbol facts.
A successful identity has the explicit identityOnly capability until a checked
source producer supplies the demanded additional material. -/
def internItem (declarations : Array ItemDeclaration) (world : World) (key : InstanceKey) :
    Except String (World × CallInstance) := do
  validateItemSource declarations world key
  if let some id := findItem world key then
    let actual ← keyOf world id
    unless actual == key do throw "source instance interner key contradiction"
    return (world,id)
  checkDefinition key.definition
  let matching := declarations.filter (·.definition == key.definition)
  unless matching.size == 1 do throw "source Item declaration absent or ambiguous"
  let some declaration := matching[0]? | throw "source Item declaration absent"
  -- Both source kinds denote an Item identity. Associated declarations here
  -- identify the supplied DefId; this constructor never selects a trait impl.
  match declaration.kind with
  | .function | .associatedFunction => pure ()
  checkArguments world declaration.parameters key.arguments
  let (canonical,definition) := match world.canonical.definitions.findIdx? (· == key.definition) with
    | some id => (world.canonical,id)
    | none => ({world.canonical with definitions := world.canonical.definitions.push key.definition},
        world.canonical.definitions.size)
  let id := canonical.instances.size
  let value : InstanceNode := {
    instanceKind := .Item definition, genericArgs := key.arguments, id,
    kind := .identityOnly, defPath := some declaration.path, definitionId := some definition,
    bodyId := none, promotedBodies := #[] }
  LocalValidation.validateInstance value
  return ({world with
    canonical := {canonical with instances := canonical.instances.push value}
    keys := world.keys.push (key,id)},id)

/-- Missing body capability remains an error, including promoted-body queries;
identityOnly's empty storage is never interpreted as a no-promotions answer. -/
def bodyId (world : World) (id : CallInstance) : Except String BodyId := do
  let value ← node world id
  unless value.kind == .instanceMir do throw "source Item executable body has not been derived"
  let some body := value.bodyId | throw "source Item body identity absent"
  let some actual := world.canonical.bodies[body]? | throw "source Item body absent"
  unless actual.instanceId == id do throw "source Item body/instance mismatch"
  return body
/-- Repeating an already validated canonical key is an exact no-op, for any
source declaration frontier. It cannot reserve another handle or a body slot. -/
theorem internItem_existing (declarations : Array ItemDeclaration) (world : World)
    (key : InstanceKey) (id : CallInstance)
    (sourceValid : validateItemSource declarations world key = .ok ())
    (found : findItem world key = some id) (identity : keyOf world id = .ok key) :
    internItem declarations world key = .ok (world,id) := by
  simp [internItem, sourceValid, found, identity]
  change (if key = key then Except.ok (world,id) else _) = _
  simp
end Miri.Input.SourceCompilerWorld
