import Miri.Input.Decoder
import Miri.Input.CoroutineBodyWorld
import Miri.Input.SourceMir

/-! Full runtime body construction from actual raw coroutine templates. Oracle
spans join by exact compiler lo/hi/context; instruction scopes remain unchanged.
The oracle body comes from independent rustc instance MIR normalization. -/
open Lean Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def remapSpans (mapping : Array Nat) : Nat → Json → Except String Json
  | 0,_ => throw "span remap exhausted"
  | fuel+1,.arr values => .arr <$> values.mapM (remapSpans mapping fuel)
  | fuel+1,.obj values => do
    let entries ← values.toArray.mapM fun (key,value) => do
      if key == "span" then
        let id ← value.getNat?
        let some id := mapping[id]? | throw "oracle span reference absent"
        pure (key,toJson id)
      else pure (key,← remapSpans mapping fuel value)
    pure (Json.mkObj entries.toList)
  | _,value => pure value

def main (args : List String) : IO Unit := do
  let [input, oraclePath] := args | throw (IO.userError "expected fresh source input and body oracle JSON")
  let document := (← must (decodeJson (← IO.FS.readFile input))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let some coverage := document.coroutineCoverage | throw (IO.userError "coroutine source catalog absent")
  let ordinary := coverage.genericSources.filter fun source => source.owner == source.physicalOwner
  let #[owner] := ordinary | throw (IO.userError "expected one ordinary coroutine source")
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 4 do throw (IO.userError "expected four normalized compiler bodies")
  for row in rows do
    let arguments ← (← must ((← must (row.getObjVal? "arguments")).getArr?)).mapM fun value =>
      must (GenericMaterialCodec.readTerm 16384 value)
    let term := GenericSubstitution.Term.definition .type "coroutine" owner.owner (Terms.ofArray arguments)
    let arena ← must (World.ofMaterial #[] #[] document.definitions document.predicates runtime.target.pointerSize.bytes.toNat)
    let (id,arena) ← must ((GenericInstantiationWorld.resolveType 16384 term).run arena)
    let instances ← must (InstanceArena.Store.ofSource arena #[])
    let initial : RuntimeArrayTypes.World := {
      metadata := runtime, arena := arena, instances := instances,
      bodies := BodyArena.Store.ofSource #[] }
    let (body,world) ← must ((CoroutineBodyWorld.intern 16384 id).run initial)
    let (again,reused) ← must ((CoroutineBodyWorld.intern 16384 id).run world)
    unless body == 0 && again == body && reused.bodies.count == 1 do
      throw (IO.userError "coroutine body identity did not remain dense and reusable")
    let .constructed (.template key) ← must (world.bodies.lookup body) |
      throw (IO.userError "coroutine body did not use exact raw template identity")
    unless key.instanceKey.definition == owner.physicalOwner do
      throw (IO.userError "coroutine physical owner differs")
    let identity := Miri.Interpreter.BodyIdentity.ofCanonicalIndex body
    let (actual,world) ← must ((SourceMir.resolveBodyIdentity identity).run world)
    let locations ← must ((← must (row.getObjVal? "spans")).getArr?)
    let mapping ← locations.mapM fun value => do
      let lo ← must ((← must (value.getObjVal? "lo")).getNat?)
      let hi ← must ((← must (value.getObjVal? "hi")).getNat?)
      let context ← must ((← must (value.getObjVal? "ctxt")).getStr?)
      let candidates := document.spans.zipIdx.filter fun (span,_) => span.lo == lo && span.hi == hi && span.context == context
      let #[( _,id)] := candidates | throw (IO.userError "compiler span correspondence absent or ambiguous")
      pure id
    let expected ← must (MirTemplateCodec.readTemplate (← must (remapSpans mapping 16384 (← must (row.getObjVal? "expected")))))
    let some source := document.mirTemplates[key.templateId]? | throw (IO.userError "selected raw template absent")
    let expectedDocument := {runtime.source with mirTemplates := document.mirTemplates.set! key.templateId {source with template := expected}}
    let expectedWorld := {world with metadata := {runtime with source := expectedDocument}}
    let (reference,_) ← must ((SourceMir.resolveBodyIdentity identity).run expectedWorld)
    unless actual.mir == reference.mir do throw (IO.userError "complete World coroutine body differs from normalized compiler oracle")
    let missing := {initial with metadata := {runtime with source := {runtime.source with mirTemplates := #[]}}}
    match (CoroutineBodyWorld.intern 16384 id).run missing with
    | .error "coroutine body raw runtime template missing or ambiguous" => pure ()
    | _ => throw (IO.userError "missing coroutine runtime template did not reject exactly")
    let duplicate := {initial with metadata := {runtime with source := {runtime.source with mirTemplates := document.mirTemplates.push source}}}
    match (CoroutineBodyWorld.intern 16384 id).run duplicate with
    | .error "coroutine body raw runtime template missing or ambiguous" => pure ()
    | _ => throw (IO.userError "duplicate coroutine runtime template did not reject exactly")
  IO.println "PASS four full source coroutine World bodies, dense reuse, missing and ambiguous physical-template controls"
