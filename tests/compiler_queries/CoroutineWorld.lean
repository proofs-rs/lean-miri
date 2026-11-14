import Miri.Input.Decoder
import Miri.Input.CoroutineBodyWorld
import Miri.Input.SourceMir

/-! Actual compiler-oracle comparisons for coroutine World layout and source
projection. Input paths are explicit; successful missing-template checks are
rejections, never successful body execution. -/
open Lean Miri.Input Miri.Input.TypeArena Miri.ABI
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def readTerm (value : Json) := must (GenericMaterialCodec.readTerm 4096 value)
private def physical (target : RuntimeTargetDataLayout) (value : Json) : IO LayoutData := do
  let source ← must (JsonReader.run DecoderValues.parseLayout value.compress)
  must ((RuntimeMetadata.layout target source).mapError toString)
private def expectError (value : Except String α) (expected : String) : IO Unit := do
  match value with
  | .ok _ => throw (IO.userError s!"expected rejection: {expected}")
  | .error actual => unless actual == expected do
      throw (IO.userError s!"wrong rejection: {actual}; expected {expected}")

def main (args : List String) : IO Unit := do
  let [input, oraclePath] := args | throw (IO.userError "expected input JSON and independent oracle JSON")
  let document := (← must (decodeJson (← IO.FS.readFile input))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let oracle ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let mut count := 0
  let mut fields := 0
  let mut runtimeBodies := 0
  let mut missingBodies := 0
  for owner in oracle do
    for row in ← must ((← must (owner.getObjVal? "oracle")).getArr?) do
      let term ← readTerm (← must (row.getObjVal? "type"))
      -- All type/constant identities are constructed outside the material
      -- prefixes. Definitions retain declaration source and raw DefPath data.
      let empty ← must (World.ofMaterial #[] #[] document.definitions document.predicates runtime.target.pointerSize.bytes.toNat)
      let (id, world) ← must ((GenericInstantiationWorld.resolveType 4096 term).run empty)
      if count == 0 then
        let wrappers := document.definitions.zipIdx.filter fun (definition,_) =>
          definition.adtDeclaration.any (·.langItem == some "manually_drop")
        let #[(wrapper,index)] := wrappers | throw (IO.userError "ManuallyDrop source declaration missing or ambiguous")
        let missingDocument := {document with definitions := document.definitions.set! index {wrapper with sourceEnvironment := none}}
        let missingRuntime ← must ((RuntimeMetadata.ofDocument missingDocument).mapError toString)
        let missingWorld ← must (World.ofMaterial #[] #[] missingDocument.definitions missingDocument.predicates runtime.target.pointerSize.bytes.toNat)
        let (missingId,missingWorld) ← must ((GenericInstantiationWorld.resolveType 4096 term).run missingWorld)
        expectError ((RuntimeMetadata.layoutInWorld missingRuntime missingId).run missingWorld)
          "raw source environment declaration is absent"
      let (actual, world) ← must ((RuntimeMetadata.layoutInWorld runtime id).run world)
      let expected ← physical runtime.target (← must (row.getObjVal? "layout"))
      unless actual.layout == expected do throw (IO.userError "complete source coroutine World layout differs")
      let some coverage := document.coroutineCoverage | throw (IO.userError "coroutine sources missing")
      let selected ← must (CoroutineSourceInstantiation.instantiate coverage.genericSources 4096 term)
      let savedLayouts ← must ((← must (row.getObjVal? "saved_layouts")).getArr?)
      for (variant, variantIndex) in selected.source.layout.variants.zipIdx do
        let (parent, world) ← must ((RuntimeMetadata.variantLayoutInWorld runtime actual variantIndex).run world)
        for (saved, index) in variant.zipIdx do
          let (field, world) ← must ((RuntimeMetadata.fieldLayoutForInWorld runtime parent index).run world)
          let some expected := savedLayouts[saved]? | throw (IO.userError "oracle saved field absent")
          unless field.layout == (← physical runtime.target expected) do throw (IO.userError "source coroutine state field differs")
          unless (← must (GenericInstantiationWorld.ofType world 4096 field.ty)) == (← must (selected.stateField variantIndex index)) do
            throw (IO.userError "source coroutine state field identity differs")
          fields := fields + 1
      for (upvar, index) in selected.upvars.zipIdx do
        let (field, world) ← must ((RuntimeMetadata.fieldLayoutForInWorld runtime actual index).run world)
        unless (← must (GenericInstantiationWorld.ofType world 4096 field.ty)) == upvar do
          throw (IO.userError "source coroutine outer upvar differs")
        fields := fields + 1
      -- Each physical owner either retains its exact raw runtime template or
      -- rejects. Auxiliary drop snapshots cannot supply the missing capability.
      let compilerWorld : RuntimeArrayTypes.World := {
        metadata := runtime, arena := world,
        instances := ← must (InstanceArena.Store.ofSource world #[]),
        bodies := BodyArena.Store.ofSource #[] }
      let physical ← must (world.definitionRef selected.source.physicalOwner)
      let templates := document.mirTemplates.filter fun source =>
        source.definitionId == physical && source.sourceRole == .runtime && source.sourcePromoted.isNone
      if templates.isEmpty then
        expectError ((CoroutineBodyWorld.intern 4096 id).run compilerWorld)
          "coroutine body raw runtime template missing or ambiguous"
        missingBodies := missingBodies + 1
      else
        let (body,retained) ← must ((CoroutineBodyWorld.intern 4096 id).run compilerWorld)
        let .constructed (.template key) ← must (retained.bodies.lookup body) |
          throw (IO.userError "coroutine body did not retain a raw runtime template identity")
        unless key.instanceKey.definition == selected.source.physicalOwner && key.role == .runtime do
          throw (IO.userError "coroutine body selected an auxiliary or wrong physical source")
        let identity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex body
        let (constructed,_) ← must ((SourceMir.resolveBodyIdentity identity).run retained)
        unless constructed.sourceRole == .runtime && constructed.definitionId == some physical &&
            !constructed.mir.locals.isEmpty && !constructed.mir.basicBlocks.isEmpty do
          throw (IO.userError "raw coroutine runtime body construction did not retain complete source identity")
        runtimeBodies := runtimeBodies + 1
      expectError ((RuntimeMetadata.fieldTypeInWorld runtime id selected.source.layout.variants.size 0).run world)
        "coroutine state variant index absent"
      count := count + 1
  unless count > 0 do throw (IO.userError "empty oracle")
  IO.println s!"PASS {count} complete coroutine World layouts, {fields} source projections, {runtimeBodies} raw runtime bodies and {missingBodies} exact missing-template rejections"
