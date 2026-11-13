import Miri.Input.Decoder
import Miri.Input.SourceMirCall

/-! Full actual raw-source bodies are constructed outside all material type,
constant, instance and body prefixes. Oracle spans join by exact lo/hi/context.
Direct-call callbacks must retain and reuse the same execution-owned World. -/
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def remapSpans (mapping : Array Nat) : Nat → Json → Except String Json
  | 0,_ => throw "span remap exhausted"
  | fuel+1,.arr values => .arr <$> values.mapM (remapSpans mapping fuel)
  | fuel+1,.obj values => do
    let entries ← values.toArray.mapM fun (key,value) => do
      if key == "span" || key == "constant_span" || key == "function_span" then
        let some id := mapping[← value.getNat?]? | throw "oracle span reference absent"
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
  let [input,oraclePath,excludedPath] := args | throw (IO.userError "expected fresh source input, retained oracle and unsupported oracle")
  let document := (← must (decodeJson (← IO.FS.readFile input))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 41 do throw (IO.userError "expected 41 complete source-body comparisons")
  let excluded ← must ((← must (Json.parse (← IO.FS.readFile excludedPath))).getArr?)
  unless excluded.size == 1 do throw (IO.userError "expected one explicit unsupported oracle row")
  for row in excluded do
    unless (← must ((← must (row.getObjVal? "name")).getStr?)) == "raw_pointer" do
      throw (IO.userError "unsupported oracle domain changed")
    let owner ← must (row.getObjVal? "physical_owner")
    let owner : GenericSubstitution.DefinitionIdentity := ⟨
      ← must ((← must (owner.getObjVal? "crate")).getNat?),
      ← must ((← must (owner.getObjVal? "index")).getNat?)⟩
    let empty ← must (World.ofMaterial #[] #[] document.definitions document.predicates runtime.target.pointerSize.bytes.toNat)
    match empty.definitionRef owner with
    | .error "type universe physical definition is absent or duplicated" => pure ()
    | .error error => throw (IO.userError s!"wrong unsupported physical-source rejection: {error}")
    | .ok _ => throw (IO.userError "unsupported raw_pointer unexpectedly acquired physical source")
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
    let empty ← must (World.ofMaterial #[] #[] document.definitions document.predicates runtime.target.pointerSize.bytes.toNat)
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
    let mut retained := world
    for block in [:actual.mir.basicBlocks.size] do
      let (seed,updated) ← must ((SourceMirCall.sourceIdentity identity block).run retained)
      retained := updated
      if let some seed := seed then
        let ((resolution,function),updated) ← must ((SourceMirCall.resolveInWorld document seed).run retained)
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
    let locations ← must ((← must (row.getObjVal? "spans")).getArr?)
    let mapping ← locations.mapM fun value => do
      let lo ← must ((← must (value.getObjVal? "lo")).getNat?)
      let hi ← must ((← must (value.getObjVal? "hi")).getNat?)
      let context ← must ((← must (value.getObjVal? "ctxt")).getStr?)
      let candidates := document.spans.zipIdx.filter fun (span,_) => span.lo == lo && span.hi == hi && span.context == context
      let #[(_,id)] := candidates | throw (IO.userError "oracle span has no unique compiler correspondence")
      pure id
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
  unless callbacks == 12 do throw (IO.userError s!"actual source callback domain changed: {callbacks}")
  IO.println s!"PASS 41 complete actual World bodies and {callbacks} persistent direct-call callbacks; missing/ambiguous sources reject; one raw_pointer expected Unsupported"
