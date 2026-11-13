import Miri.Input.Decoder
import Miri.Input.SourceMirCall

/-! Full actual raw-source bodies are constructed outside all material type,
constant, instance and body prefixes. Oracle spans join by exact lo/hi/context.
Direct-call callbacks must retain and reuse the same execution-owned World. -/
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def remapSpans (mapping : Array (Option Nat)) : Nat → Json → Except String Json
  | 0,_ => throw "span remap exhausted"
  | fuel+1,.arr values => .arr <$> values.mapM (remapSpans mapping fuel)
  | fuel+1,.obj values => do
    let entries ← values.toArray.mapM fun (key,value) => do
      if key == "span" || key == "constant_span" || key == "function_span" then
        let some (some id) := mapping[← value.getNat?]? | throw "oracle span reference absent"
        pure (key,toJson id)
      else pure (key,← remapSpans mapping fuel value)
    pure (Json.mkObj entries.toList)
  | _,value => pure value
private def sourceFor (document : ImportDocument) (physical : Nat) : Except String (CopyTemplateSource × Nat) := do
  let candidates := document.mirTemplates.zipIdx.filter fun (source,_) =>
    source.definitionId == physical && source.sourceRole == .runtime && source.sourcePromoted.isNone
  let #[(source,index)] := candidates | throw "exact raw runtime source missing or ambiguous"
  pure (source,index)

def main (args : List String) : IO Unit := do
  let (input,oraclePath,expectMissing) ← match args with
    | [input,oraclePath] => pure (input,oraclePath,false)
    | [input,oraclePath,"expect-missing-impl-source"] => pure (input,oraclePath,true)
    | _ => throw (IO.userError "expected source input, independent oracle and optional expect-missing-impl-source")
  let document := (← must (decodeJson (← IO.FS.readFile input))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let row ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows := #[row]
  let mut callbacks := 0
  for row in rows do
    unless (← must ((← must (row.getObjVal? "source_role")).getStr?)) == "runtime" do
      throw (IO.userError "oracle source role changed")
    let owner ← must (row.getObjVal? "physical_owner")
    let owner : GenericSubstitution.DefinitionIdentity := ⟨
      ← must ((← must (owner.getObjVal? "crate")).getNat?),
      ← must ((← must (owner.getObjVal? "index")).getNat?)⟩
    let terms ← (← must ((← must (row.getObjVal? "arguments")).getArr?)).mapM fun value =>
      must (GenericMaterialCodec.readTerm 16384 value)
    let empty ← must (World.ofMaterial #[] #[] document.definitions #[] runtime.target.pointerSize.bytes.toNat)
    let (arguments,arena) ← must ((GenericInstantiationWorld.resolveArguments 16384 terms).run empty)
    let physical ← must (arena.definitionRef owner)
    let (source,templateId) ← must (sourceFor document physical)
    let instances ← must (InstanceArena.Store.ofSource arena #[])
    let initial : RuntimeArrayTypes.World := {
      metadata := runtime,arena := arena,instances := instances,
      bodies := BodyArena.Store.ofSource #[] }
    let action : RuntimeArrayTypes.CompilerM (Nat × Nat) := do
      let sourceInstance ← RuntimeArrayTypes.internInstance (.Item physical) arguments
      pure (sourceInstance,← RuntimeArrayTypes.internBody templateId sourceInstance none .runtime)
    let ((sourceInstance,body),world) ← must (action.run initial)
    let ((again,bodyAgain),reused) ← must (action.run world)
    unless sourceInstance == 0 && again == sourceInstance && body == 0 && bodyAgain == body &&
        reused.instances.constructed.size == 1 && reused.bodies.count == 1 do
      throw (IO.userError "raw source identities did not remain dense and reusable")
    let identity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex body
    let (actual,world) ← must ((SourceMir.resolveBodyIdentity identity).run world)
    unless actual.definitionId == some physical && actual.sourceRole == .runtime do
      throw (IO.userError "raw runtime body physical owner/role differs")
    let locations ← must ((← must (row.getObjVal? "spans")).getArr?)
    let mapping ← locations.mapM fun value => do
      let lo ← must ((← must (value.getObjVal? "lo")).getNat?)
      let hi ← must ((← must (value.getObjVal? "hi")).getNat?)
      let context ← must ((← must (value.getObjVal? "ctxt")).getStr?)
      let candidates := document.spans.zipIdx.filter fun (span,_) => span.lo == lo && span.hi == hi && span.context == context
      if candidates.size > 1 then throw (IO.userError "oracle span has ambiguous compiler correspondence")
      -- A missing selected-body span is expected in the root-only negative.
      -- Every span actually used by a compared body must still resolve below.
      pure (candidates[0]?.map (·.2))
    let mut retained := world
    for block in [:actual.mir.basicBlocks.size] do
      let (seed,updated) ← must ((SourceMirCall.sourceIdentity identity block).run retained)
      retained := updated
      if let some seed := seed then
        let ((resolution,function),updated) ← must ((SourceMirCall.resolveInWorld document seed).run retained)
        let selected ← must (CompilerInstance.source updated resolution.instanceId)
        let selectedOwner ← must (row.getObjVal? "selected_method")
        unless selected.definition.crateIndex == (← must ((← must (selectedOwner.getObjVal? "crate")).getNat?)) &&
            selected.definition.index == (← must ((← must (selectedOwner.getObjVal? "index")).getNat?)) do
          throw (IO.userError "source trait resolution differs from independent rustc selection")
        let .Item _ := selected.kind | throw (IO.userError "concrete trait selection fabricated a non-Item")
        if expectMissing then
          unless (sourceFor document selected.kind.defId).toOption.isNone do
            throw (IO.userError "root-only export unexpectedly retained impl source")
        else
          let (targetSource,targetTemplate) ← must (sourceFor document selected.kind.defId)
          let (targetBody,targetWorld) ← must ((RuntimeArrayTypes.internBody targetTemplate resolution.instanceId none .runtime).run updated)
          let (target,_) ← must ((SourceMir.resolveBodyIdentity (Miri.Interpreter.BodyIdentity.ofCanonicalIndex targetBody)).run targetWorld)
          unless target.sourceRole == .runtime do throw (IO.userError "selected impl lost its raw runtime body")
          let targetExpected ← must (MirTemplateCodec.readTemplate (← must (remapSpans mapping 16384 (← must (row.getObjVal? "selected_expected")))))
          let targetReferenceWorld := {targetWorld with metadata := {runtime with source := {runtime.source with
            mirTemplates := runtime.source.mirTemplates.set! targetTemplate {targetSource with template := targetExpected}}}}
          let (targetReference,_) ← must ((SourceMir.resolveBodyIdentity (Miri.Interpreter.BodyIdentity.ofCanonicalIndex targetBody)).run targetReferenceWorld)
          unless target.mir == targetReference.mir do
            throw (IO.userError "complete selected impl World body differs from independent normalized compiler body")
          unless (sourceFor {document with mirTemplates := document.mirTemplates.push targetSource} selected.kind.defId).toOption.isNone do
            throw (IO.userError "ambiguous selected impl source admitted")
        let some actualBlock := actual.mir.basicBlocks[block]? | throw (IO.userError "actual call block absent")
        let .Call expected .. := actualBlock.terminator.kind |
          throw (IO.userError "symbolic source call did not construct a Call terminator")
        unless function == expected do throw (IO.userError "source callback function identity differs from full actual body")
        let ((again,functionAgain),repeated) ← must ((SourceMirCall.resolveInWorld document seed).run updated)
        unless again.instanceId == resolution.instanceId && again.functionType == resolution.functionType &&
            again.arguments == resolution.arguments && functionAgain == function &&
            repeated.instances.constructed.size == updated.instances.constructed.size &&
            repeated.arena.typeCount == updated.arena.typeCount do
          throw (IO.userError "source callback lost or duplicated execution-owned identities")
        retained := repeated
        callbacks := callbacks + 1
    let expected ← must (MirTemplateCodec.readTemplate (← must (remapSpans mapping 16384 (← must (row.getObjVal? "expected")))))
    let expectedDocument := {runtime.source with mirTemplates := runtime.source.mirTemplates.set! templateId {source with template := expected}}
    let expectedWorld := {retained with metadata := {runtime with source := expectedDocument}}
    let (reference,_) ← must ((SourceMir.resolveBodyIdentity identity).run expectedWorld)
    unless actual.mir == reference.mir do throw (IO.userError "complete actual World body differs from independently normalized compiler body")
    let missingWorld := {retained with metadata := {runtime with source := {runtime.source with mirTemplates := #[]}}}
    match (SourceMir.resolveBodyIdentity identity).run missingWorld with
    | .error "raw body source template is absent" => pure ()
    | .error error => throw (IO.userError s!"wrong missing executable-source rejection: {error}")
    | .ok _ => throw (IO.userError "missing source body copied an existing material/auxiliary answer")
    unless (sourceFor {document with mirTemplates := #[]} physical).toOption.isNone &&
        (sourceFor {document with mirTemplates := document.mirTemplates.push source} physical).toOption.isNone do
      throw (IO.userError "missing or ambiguous physical source selected")
  unless callbacks == 1 do throw (IO.userError s!"actual source callback domain changed: {callbacks}")
  if expectMissing then
    IO.println "PASS complete trait caller and independent impl selection; root-only missing impl source remains Unsupported"
  else IO.println s!"PASS complete trait caller World body, {callbacks} persistent trait callback, independent impl selection and raw selected body; missing/ambiguous source guards"
