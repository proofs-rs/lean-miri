import Lean.Data.Json.FromToJson.Basic
import Miri.Input.CtfeMirSource
import Miri.Input.CompilerProviders
import Miri.Input.CompilerInitialAllocationSymbols
import Miri.Input.BodyArena
import Miri.Input.CtfeQueryBridge
import Miri.Input.RuntimeArrayTypes
import Miri.Interpreter.BodyIdentity

/-! Preparation-only material source prefix for the genuine nongeneric external
u64 unary-Not leaf. This constructor STARTS from compiler.initialTypes; query
execution cannot append to an existing execution-owned material prefix. -/
namespace Miri.Input.CompilerColdU64Source
open Lean Miri.MIR Miri.Interpreter CompilerInitialAllocation
set_option autoImplicit false
structure Registered where
  private mk ::
  definition : GenericSubstitution.DefinitionIdentity
  environment : CompilerTypingEnv.Env
  callee : CallInstance
  instanceKey : InstanceArena.Key
  body : LoadedBody
  source : Body
  raw : CtfeMirSource.Source
  type : TypeId
/-- A selected PA ALLOC/VALTREE boundary, NOT a VALUE-query freshness cap. -/
structure ColdBoundary where
  private mk ::
  definition : GenericSubstitution.DefinitionIdentity
  next : UInt64
  globalCount : Nat
  dedupCount : Nat

/-- Source producer/independent oracle observes the exact selected keys without
calling a provider. Incremental restoration is excluded for this cold slice. -/
def ColdBoundary.read (source : Registered) (j : Json) : Except String ColdBoundary := do
  let names := ["schema","phase","source_definition","typing_mode","param_env_count","arguments","promoted",
    "pa_allocation_present","pa_valtree_present","incremental_enabled","on_disk_cache_enabled",
    "next_source_alloc_id","global_count","dedup_count","source_acquisition_unchanged"]
  let actual := (← j.getObj?).toArray.map (·.1)
  unless actual.size == names.length && actual.all names.contains do throw "u64 cold boundary field set differs"
  unless (← j.getObjValAs? String "schema") == "selected_u64_pa_allocation_boundary_v1" &&
      (← j.getObjValAs? String "phase") == "before_source_queries" &&
      (← j.getObjValAs? String "typing_mode") == "post_analysis" &&
      (← j.getObjValAs? Nat "param_env_count") == 0 &&
      (← (← j.getObjVal? "arguments").getArr?).isEmpty && (← j.getObjVal? "promoted") == .null do
    throw "u64 cold boundary schema/PA key differs"
  let definitionJson ← j.getObjVal? "source_definition"
  let definitionFields := (← definitionJson.getObj?).toArray.map (·.1)
  unless definitionFields.size == 2 && definitionFields.all (["crate","index"].contains) do
    throw "u64 cold boundary definition field set differs"
  let definition ← GenericMaterialCodec.readDefinition definitionJson
  unless definition == source.definition do throw "u64 cold boundary physical source differs"
  for flag in ["pa_allocation_present","pa_valtree_present","incremental_enabled","on_disk_cache_enabled"] do
    if ← j.getObjValAs? Bool flag then throw s!"u64 cold key unavailable: {flag}"
  unless ← j.getObjValAs? Bool "source_acquisition_unchanged" do
    throw "u64 source acquisition needs actual effect replay"
  let next ← j.getObjValAs? Nat "next_source_alloc_id"
  unless next > 0 && next < 2^64 do throw "u64 cold boundary frontier out of range"
  pure ⟨definition,UInt64.ofNat next,← j.getObjValAs? Nat "global_count",← j.getObjValAs? Nat "dedup_count"⟩

def Registered.allocationKey (source : Registered) : CtfeQueryBridge.QueryKey :=
  ⟨.allocation,source.environment,⟨source.instanceKey,none⟩⟩

structure Prepared where
  registered : Registered
  types : RuntimeArrayTypes.World

private def rawInstance (definition : GenericSubstitution.DefinitionIdentity) : Json :=
  Json.mkObj [("kind",Json.mkObj [("kind",toJson "item"),("definition",Json.mkObj
    [("crate",toJson definition.crateIndex),("index",toJson definition.index)])]),("arguments",Json.arr #[])]

/-- Actual canonical source rows must already be in the input metadata.
Byte-position-only standalone probes fail validateReferences; no span0 or
crate0 remapping is available here. Existing material body IDs remain a prefix. -/
def prepare (compiler : CompilerProviders.Prepared) (frame : CtfeMirSource.Source) : Except String Prepared := do
  let initial ← compiler.initialTypes
  CtfeMirSource.validate frame
  let .rawU64 program := frame.program | throw "u64 leaf requires raw-u64 source program"
  unless frame.policy == .rawU64 && frame.role == .ctfe && frame.definition.crateIndex != 0 &&
      frame.promoted.isNone && frame.parameters.isEmpty && frame.requiredConstants.isEmpty &&
      program.ownerKind == .associatedConstant && program.required.isEmpty do
    throw "cold u64 leaf requires an external nongeneric unpromoted AssocConst with empty preamble"
  unless program.localCount == 1 && frame.localMutability == #[true] && program.statements.size == 1 do
    throw "cold u64 leaf requires its actual single return local/statement"
  let some (RawU64Frame.Statement.assign 0 (RawU64Frame.Rvalue.unaryNot (RawU64Frame.Operand.sourceValue literal))) := program.statements[0]?
    | throw "cold u64 leaf requires actual UnaryOp.Not(source literal)"
  unless literal.kind == .literalValue && literal.userType.isNone do
    throw "cold u64 leaf cannot reuse a type-value/compiler-result literal"
  let known := fun identity => initial.metadata.source.definitions.any
    (fun row => row.crateIndex == identity.crateIndex && row.index == identity.index)
  CtfeMirSource.validateReferences initial.metadata.source.spans.size known frame
  unless program.preambleDefSpan.id < initial.metadata.source.spans.size do
    throw "u64 leaf canonical preamble span absent"
  if frame.scopes.any (fun scope => scope.lintRoot.isSome) then
    throw "u64 external leaf lint-owner material outside this diagnostic scope"
  let lookup : SourceEnvironment.Lookup := fun identity => do
    let some row := initial.metadata.source.definitions.find? (fun row => row.crateIndex == identity.crateIndex && row.index == identity.index)
      | throw "u64 source declaration physical owner absent"
    let some value := row.sourceEnvironment | throw "u64 source declaration environment absent"
    pure value
  let clauses ← SourceEnvironment.instantiate lookup 16384 frame.definition #[]
  unless clauses.isEmpty do throw "u64 leaf requires actual empty declaration ParamEnv"
  let (instanceKey,arena) ← (RawSymbols.decodeInstance (rawInstance frame.definition)).run initial.arena
  let .Item definition := instanceKey.kind | throw "u64 leaf callee is not actual Item"
  unless instanceKey.definition == frame.definition && instanceKey.arguments.isEmpty do
    throw "u64 leaf physical instance mismatch"
  let term : GenericSubstitution.Term := .atom .type "uint" "u64"
  let (type,arena) ← (GenericInstantiationWorld.resolveType 16384 term).run arena
  let shape ← match ← arena.lookupType type with
    | .constructed value => pure (some value) | .material node => arena.materialKey node
  unless shape == some (.integer false .u64) do throw "u64 source did not resolve actual World u64"
  let world := {initial with arena}
  let (callee,world) ← (RuntimeArrayTypes.internInstance instanceKey.kind instanceKey.arguments).run world
  unless world.bodies.constructed.isEmpty && world.bodies.materialCount == world.metadata.source.bodies.size do
    throw "u64 source material prefix must be assembled before constructed/query bodies exist"
  let some statementInfo := frame.statementSources[0]? >>= (·[0]?)
    | throw "u64 source statement location absent"
  let some terminatorInfo := frame.terminatorSources[0]? | throw "u64 source Return location absent"
  let constant : Miri.MIR.Operand := .Constant ⟨literal.span,none,.Val (.Scalar (.Int literal.value.toNat 8)) type⟩
  let block : Miri.MIR.BasicBlock := {
    statements := #[⟨statementInfo,.Assign ⟨0,#[]⟩ (.UnaryOp .Not constant)⟩]
    terminator := ⟨terminatorInfo,.Return⟩
    cleanup := false }
  let mir : Miri.MIR.Body := {
    phase := frame.phase
    argumentCount := 0
    spreadArgument := none
    locals := #[type]
    basicBlocks := #[block] }
  let source : Body := {
    definitionId := some definition,defPath := program.defPath,sourcePath := "$ctfe_scalar_sources",
    spanId := frame.span.id,preambleDefSpanId := program.preambleDefSpan.id,injectionPhase := none,
    localSources := frame.localSources.map (fun info => ⟨info.span.id,info.scope⟩),
    sourceScopes := frame.scopes.mapIdx (fun id scope => ⟨id,scope.parent,scope.span.id,none,none⟩),
    backtraceSpans := #[],callEvidence := #[],nodeFacts := #[#[]],requiredConsts := #[],
    sourceRole := .ctfe,mir := mir,instanceId := callee,promotedBodies := #[] }
  let index := world.metadata.source.bodies.size
  let document := {world.metadata.source with bodies := world.metadata.source.bodies.push (.material source)}
  let metadata := {world.metadata with source := document}
  let world := {world with metadata,bodies := BodyArena.Store.ofSource document.bodies}
  pure ⟨⟨frame.definition,⟨⟨clauses⟩,.postAnalysis⟩,callee,instanceKey,
    ⟨BodyIdentity.ofCanonicalIndex index,mir⟩,source,frame,type⟩,world⟩

/-- Query-time verification ONLY reads the established preparation prefix. -/
def verify (source : Registered) (world : RuntimeArrayTypes.World) : Except String Unit := do
  unless source.environment.mode == .postAnalysis && source.environment.paramEnv.callerBounds.isEmpty do
    throw "u64 query execution is not the prepared empty PA environment"
  let shape ← match ← world.arena.lookupType source.type with
    | .constructed value => pure (some value) | .material node => world.arena.materialKey node
  unless shape == some (.integer false .u64) do throw "u64 current return type World changed"
  let actual ← match ← world.instances.lookup source.callee with
    | .material key | .constructed key => pure key
  unless actual == source.instanceKey && actual.definition == source.definition do
    throw "u64 current instance World changed"
  let .material index ← world.bodies.lookup source.body.identity.index
    | throw "u64 prepared source lost canonical material identity"
  let some (.material body) := world.metadata.source.bodies[index]?
    | throw "u64 prepared material source row absent"
  unless index == source.body.identity.index && body.sourceRole == .ctfe &&
      body.instanceId == source.callee && body.definitionId == some source.instanceKey.kind.defId &&
      body.mir == source.body.body && body.mir == source.source.mir do
    throw "u64 source role/physical owner/body identity mismatch"
end Miri.Input.CompilerColdU64Source
