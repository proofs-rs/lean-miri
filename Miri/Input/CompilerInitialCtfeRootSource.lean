import Miri.Input.CompilerInitialAllocationSymbols
import Miri.Input.CompilerInitialAllocationCodec
import Miri.Input.CtfeQueryBridge
import Miri.Input.Decoder
import Miri.Input.LowerMIR
import Miri.Input.SourceEnvironment
import Miri.Input.CompilerInitialCtfeFreshGuard

/-! Genuine mir_for_ctfe root source. Inline full MIR is parsed against this
actual document's pools and contextualized ONLY with an execution-interned
callee. The body is registered under a real BodyArena key with role=ctfe;
runtime SourceMir role guards remain intact. The bounded source transform is
checked by exact equality with the original decoded MIR after instantiation. -/
namespace Miri.Input.CompilerInitialCtfeRootSource
open Lean Miri.MIR Miri.Interpreter CompilerInitialAllocation
set_option autoImplicit false
structure Prepared where
  private mk ::
  freshness : CompilerInitialCtfeFreshGuard.Fresh
  initialNext : UInt64
  query : CtfeQueryBridge.QueryKey
  callee : CallInstance
  body : LoadedBody
  source : Body
  key : BodyArena.Key
  types : RuntimeArrayTypes.World

/-- Persistent source identity/body only. In particular this does not retain
Prepared.types from source admission; runtime query callbacks use the current
execution-owned type/instance/body arena explicitly. -/
structure Registered where
  private mk ::
  freshness : CompilerInitialCtfeFreshGuard.Fresh
  initialNext : UInt64
  query : CtfeQueryBridge.QueryKey
  callee : CallInstance
  body : LoadedBody
  source : Body
  key : BodyArena.Key

def Prepared.registered (source : Prepared) : Registered :=
  ⟨source.freshness,source.initialNext,source.query,source.callee,source.body,source.source,source.key⟩

private def exactFields (j : Json) (names : List String) : Except String Unit := do
  let actual := (← j.getObj?).toArray.map (·.1)
  unless actual.size == names.length && actual.all names.contains do throw "CTFE root header field set differs"
private def place (value : Miri.MIR.Place) : Except String MirTemplate.SourcePlace := do
  unless value.projection.isEmpty do throw "literal CTFE root projection unsupported"
  pure ⟨value.localId,#[]⟩
private def operand (ty : TypeId) : Miri.MIR.Operand → Except String MirTemplate.SourceOperand
  | .Copy value => .copy <$> place value
  | .Move value => .move <$> place value
  | .Constant value => do
    unless value.userType.isNone do throw "literal CTFE root has source annotation"
    let .Val (.Scalar (.Int bits bytes)) declared := value.value
      | throw "literal CTFE root constant is not raw Val(ScalarInt)"
    unless declared == ty && bytes == 4 && bits < 2^32 do throw "literal CTFE root constant type/width mismatch"
    pure (.scalar ⟨0⟩ value.span bits bytes)
  | _ => .error "literal CTFE root operand outside source domain"
private def template (ty : TypeId) (rawType : GenericSubstitution.Term) (body : Body) :
    Except String MirTemplate.Template := do
  unless body.mir.argumentCount == 0 && body.mir.spreadArgument.isNone &&
      body.mir.locals.all (· == ty) && !body.mir.locals.isEmpty &&
      body.requiredConsts.isEmpty do throw "literal CTFE root local/argument/required-constant domain mismatch"
  unless body.mir.basicBlocks.size == 1 do throw "literal CTFE root requires one source block"
  let blocks ← body.mir.basicBlocks.mapM fun block => do
    unless !block.cleanup && block.terminator.kind == .Return do throw "literal CTFE root requires normal Return"
    let statements ← block.statements.mapM fun statement => do
      let kind ← match statement.kind with
        | .StorageLive id => pure (MirTemplate.StatementKind.storageLive id)
        | .StorageDead id => pure (.storageDead id)
        | .Nop => pure .nop
        | .Assign destination (.Use value retag) => do
          pure (.sourceAssign (← place destination) (.use (← operand ty value) retag))
        | _ => throw "literal CTFE root statement outside source domain"
      pure ({source := statement.sourceInfo,kind := kind} : MirTemplate.Statement)
    pure ({statements,terminator := ⟨block.terminator.sourceInfo,.«return»⟩,cleanup := false} : MirTemplate.Block)
  pure {parameters := #[],types := #[rawType],skeleton := {
    phase := body.mir.phase,argumentCount := 0,spreadArgument := none,
    locals := body.mir.locals.map (fun _ => ⟨0⟩),blocks := blocks}}

def prepare (text : String) (initialNext : UInt64) (initialDedup : Nat) (row : Json) (initial : RuntimeArrayTypes.World) :
    Except String Prepared := do
  exactFields row ["policy","source_role","source_definition_kind","source_definition","source_instance","source_promoted","return_type","body","source_acquisition_effects","initial_query_cache"]
  unless (← (← row.getObjVal? "policy").getStr?) == "literal_u32_ctfe_raw_v1" &&
      (← (← row.getObjVal? "source_role").getStr?) == "ctfe" &&
      (← row.getObjVal? "source_promoted") == .null do throw "CTFE root policy/role/promoted mismatch"
  let kind ← (← row.getObjVal? "source_definition_kind").getStr?
  unless kind == "const" || kind == "associated_const" do throw "raw root must be a Const/AssocConst source definition"
  let physical ← GenericMaterialCodec.readDefinition (← row.getObjVal? "source_definition")
  let freshness ← CompilerInitialCtfeFreshGuard.read physical (← row.getObjVal? "initial_query_cache")
  let (instanceKey,arena) ← (RawSymbols.decodeInstance (← row.getObjVal? "source_instance")).run initial.arena
  let .Item _ := instanceKey.kind | throw "CTFE root requires an Item source callee"
  unless instanceKey.definition == physical && instanceKey.arguments.isEmpty do throw "CTFE root physical callee mismatch"
  let lookup : SourceEnvironment.Lookup := fun identity => do
    let some source := initial.metadata.source.definitions.find? (fun source => source.crateIndex == identity.crateIndex && source.index == identity.index)
      | throw "CTFE root declaration scope absent"
    let some material := source.sourceEnvironment | throw "CTFE root raw declaration predicates absent"
    pure material
  let clauses ← SourceEnvironment.instantiate lookup 16384 physical #[]
  unless clauses.isEmpty do throw "CTFE literal root requires empty source declaration predicates"
  let rawType ← GenericMaterialCodec.readTerm 1024 (← row.getObjVal? "return_type")
  let (ty,arena) ← (GenericInstantiationWorld.resolveType 16384 rawType).run arena
  let shape ← match ← arena.lookupType ty with
    | .constructed value => pure (some value) | .material node => arena.materialKey node
  unless shape == some (.integer false .u32) do throw "CTFE root return type is not actual World u32"
  let world := {initial with arena}
  let (callee,world) ← (RuntimeArrayTypes.internInstance instanceKey.kind instanceKey.arguments).run world
  let bodyJson ← row.getObjVal? "body"
  if (bodyJson.getObjVal? "instance_id").isOk then throw "raw CTFE body must not supply a runtime callee ID"
  let contextual := bodyJson.setObjVal! "instance_id" (toJson callee)
  let parsed ← JsonReader.run (DecodeMIR.parseBody "$compiler_initial_ctfe_roots.body" none) contextual.compress
  let context : DecodeMIR.Context := {
    typeCount := world.arena.typeCount,allocationCount := world.metadata.source.allocations.size,
    definitionCount := world.metadata.source.definitions.size,typeConstantCount := world.arena.constantCount,
    spanCount := world.metadata.source.spans.size,scalarSize := fun id => if id == ty then some 4 else none}
  let source ← DecodeMIR.resolveBody context parsed
  unless source.sourceRole == .ctfe && source.instanceId == callee &&
      source.definitionId == some instanceKey.kind.defId do throw "actual CTFE body owner/role/callee differs"
  unless source.sourceScopes.all (fun scope => scope.inlined.isNone) do throw "literal CTFE root inlined source scopes unsupported"
  let rawTemplate ← template ty rawType source
  let templateId := world.metadata.source.mirTemplates.size
  let templateSource : CopyTemplateSource := {
    template := rawTemplate,definitionId := instanceKey.kind.defId,defPath := source.defPath,
    spanId := source.spanId,preambleDefSpanId := source.preambleDefSpanId,injectionPhase := source.injectionPhase,
    localSources := source.localSources,sourceScopes := source.sourceScopes,backtraceSpans := source.backtraceSpans,
    sourcePromoted := none,sourceRole := .ctfe}
  let document := {world.metadata.source with mirTemplates := world.metadata.source.mirTemplates.push templateSource}
  SourceMir.validateTemplate document templateSource
  let metadata := {world.metadata with source := document}
  let world := {world with metadata}
  let key ← BodyArena.Key.create world.arena world.instances document.mirTemplates templateId callee none .ctfe
  let (bodyId,bodies) ← world.bodies.intern world.arena world.instances document.mirTemplates document.bodies key
  let world := {world with bodies}
  let (mir,arena) ← (MirTemplate.instantiate rawTemplate 16384 #[]
    (fun term => GenericInstantiationWorld.resolveType 16384 term)).run world.arena
  unless mir == source.mir do throw "CTFE template transform changed actual decoded MIR"
  let world := {world with arena}
  let effects ← readSourceEffects (← row.getObjVal? "source_acquisition_effects")
  unless effects.unchanged && effects.beforeNext == initialNext && effects.afterNext == initialNext &&
      effects.beforeDedup == initialDedup && effects.afterDedup == initialDedup do
    throw "CTFE source acquisition allocation effects require an unsupported query-world replay"
  pure {freshness := freshness, initialNext := initialNext, query := ⟨.value,CompilerTypingEnv.fullyMonomorphized,⟨instanceKey,none⟩⟩, callee := callee, body := ⟨.ofCanonicalIndex bodyId,mir⟩, source := source, key := key, types := world}
/-- Provider-internal Codegen retry changes only the typed family/mode, never
source instance, caller bounds, body identity or MIR. -/
def forProviderKey (source : Prepared) (key : CtfeQueryBridge.QueryKey) : Except String Prepared := do
  unless key.global == source.query.global && key.environment.paramEnv == source.query.environment.paramEnv &&
      (key.environment.mode == .codegen || key.environment.mode == .postAnalysis) &&
      (key.family == .value || key.family == .allocation) do
    throw "CTFE provider key differs from selected source domain"
  pure {source with query := key}

def Registered.forProviderKey (source : Registered) (key : CtfeQueryBridge.QueryKey) : Except String Registered := do
  unless key.global == source.query.global && key.environment.paramEnv == source.query.environment.paramEnv &&
      (key.environment.mode == .codegen || key.environment.mode == .postAnalysis) &&
      (key.family == .value || key.family == .allocation) do
    throw "CTFE provider key differs from selected registered source domain"
  pure {source with query := key}

end Miri.Input.CompilerInitialCtfeRootSource
