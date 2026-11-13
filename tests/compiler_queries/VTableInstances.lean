import Miri.Input.Decoder
import Miri.Input.WorldVTableInstance
open Lean Miri.Input GenericSubstitution TraitSelection Miri.Interpreter
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def expected (row : Json) : Except String (Option WorldVTableInstance.Declaration) := do
  let kind ← (← row.getObjVal? "kind").getStr?
  if kind == "vacant" then return none
  let identity ← GenericMaterialCodec.readDefinition (← row.getObjVal? "definition")
  let arguments ← (← (← row.getObjVal? "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 2048)
  let kind ← match kind with
    | "selected" => pure WorldVTableInstance.Kind.item
    | "by_value_shim" => pure .vtable
    | "reify_none" => pure (.reify none)
    | "reify_vtable" => pure (.reify (some .Vtable))
    | _ => throw "unexpected independent oracle kind"
  pure (some ⟨kind,identity,arguments⟩)
private def reject (action : Except String α) (message : String) : IO Unit := do
  match action with
  | .ok _ => throw (IO.userError s!"missing final-instance source accepted: {message}")
  | .error actual => unless actual == message do throw (IO.userError s!"wrong final-instance rejection: {actual}; expected {message}")
def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected source and final-instance oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with compilerPredicates := #[], instances := #[], allocations := #[], functionAbis := #[], queries := {original.queries with runtime := {original.queries.runtime with virtualQueries := #[]}, vtables := #[], instanceAbis := #[], shimAbis := some #[], namedShimAbis := some #[]}}
  let context ← must (AliasRuntime.Context.ofDocument document)
  let some session := document.producer.abiSession | throw (IO.userError "raw sanitizer session missing")
  let kcfi := some (session.sanitizers.contains "kcfi")
  let metadata ← must ((RuntimeMetadata.ofDocument original).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
  let noAnswers := {metadata.source with compilerPredicates := #[], instances := #[], allocations := #[], functionAbis := #[], queries := {metadata.source.queries with runtime := {metadata.source.queries.runtime with virtualQueries := #[]}, vtables := #[], instanceAbis := #[], shimAbis := some #[], namedShimAbis := some #[]}}
  let world := {initial with instances := empty,metadata := {metadata with source := noAnswers,normalizationContext := context}}
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (oracle.getObjVal? "queries")).getArr?)
  unless rows.size == 4 do throw (IO.userError "final-instance oracle coverage changed")
  let mut total := 0
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let reference ← must (TraitSelection.Codec.readTraitRef (← must (row.getObjVal? "reference")))
    let wanted ← must ((← must ((← must (row.getObjVal? "entries")).getArr?)).mapM expected)
    unless wanted.size == 5 do throw (IO.userError "final-instance own slot count changed")
    let identities ← must (WorldDynMethods.ownMethods context 100000 2048 reference.definition)
    if name == "query_dyn" then
      -- This is ONLY the component postprocessing comparison. Object candidate
      -- selection itself must remain Unsupported in the production source query.
      let mut components := #[]
      for identity in identities do
        let index ← must (GenericInstantiation.definitionRef context.generic identity)
        let some template := context.generic.definitions[index]?.bind (·.genericTemplate)
          | throw (IO.userError "dynamic component raw method signature missing")
        let some raw := template.signatureExpression | throw (IO.userError "component signature absent")
        let signature ← must (RawFunctionSignature.read raw)
        if signature.inputs[0]? == some (.parameter .type 0) then
          components := components.push (← must (WorldVTableInstance.finish context kcfi identity (.byValueShim ⟨identity,reference.arguments⟩)))
        else
          components := components.push (some (← must (WorldVTableInstance.finishVirtual context kcfi identity reference.arguments)))
      unless components == wanted do throw (IO.userError "Virtual component postprocessing differs from rustc")
      match WorldVTableInstance.ownDeclarations context 100000 2048 kcfi reference with
      | .ok _ => throw (IO.userError "unimplemented object selection unexpectedly succeeded")
      | .error error => unless error.startsWith "dynamic trait goals" do throw (IO.userError s!"wrong dynamic residual: {error}")
      IO.println "PASS five dynamic postprocessing components; source object selection remains Unsupported"
      total := total + wanted.size
      continue
    let actual ← must (WorldVTableInstance.ownDeclarations context 100000 2048 kcfi reference)
    unless actual == wanted do throw (IO.userError s!"final declarations differ from rustc: {name}")
    let (instances,after) ← must ((WorldVTableInstance.ownInstances 100000 2048 reference).run world)
    let (again,repeated) ← must ((WorldVTableInstance.ownInstances 100000 2048 reference).run after)
    unless instances == again && after.instances.count == repeated.instances.count do
      throw (IO.userError "final-instance query did not reuse canonical identities")
    for (id,wanted) in instances.zip wanted do
      match id,wanted with
      | none,none => pure ()
      | some id,some wanted =>
        let key ← must (CompilerInstance.source after id)
        unless key.definition == wanted.definition do throw (IO.userError "World instance physical definition differs")
        let kind := match key.kind with
          | .Item _ => some WorldVTableInstance.Kind.item
          | .Shim (.VTable _) => some .vtable
          | .Shim (.Reify _ reason) => some (.reify reason)
          | _ => none
        unless kind == some wanted.kind do throw (IO.userError "World instance kind differs")
        let arguments ← must (GenericInstantiationWorld.ofArguments after.arena 2048 key.arguments)
        unless arguments == wanted.arguments do throw (IO.userError "World instance complete arguments differ")
      | _,_ => throw (IO.userError "World instance Vacant state differs")
    if name == "query_none" then
      unless actual.all (·.isNone) do throw (IO.userError "NoImpl acquired a final instance")
    else
      let some first := identities[0]? | throw (IO.userError "first source method absent")
      let some (some selected) := actual[0]? | throw (IO.userError "first selected method absent")
      let change (f : DefinitionId → DefinitionId) : AliasRuntime.Context :=
        {context with generic := {context.generic with definitions := context.generic.definitions.map fun source =>
          if source.crateIndex == selected.definition.crateIndex && source.index == selected.definition.index then f source else source}}
      let some slot := (← must (WorldVTableMethods.ownSlots context 100000 2048 reference))[0]? | throw (IO.userError "first raw slot absent")
      reject (WorldVTableInstance.finish (change fun source => {source with callableSource := none}) kcfi first slot) "vtable raw callable header absent"
      reject (WorldVTableInstance.finish (change fun source => {source with bodyTrackCaller := none}) kcfi first slot) "caller-location body codegen attribute material absent"
      reject (WorldVTableInstance.ownDeclarations context 100000 2048 none reference) "vtable reification raw sanitizer policy absent"
      reject (WorldVTableInstance.finish (change fun source => {source with callableSource := source.callableSource.map fun header =>
        {header with traitItem := some ⟨0,0⟩}}) kcfi first slot) "vtable selected impl trait method mapping mismatch"
      reject (WorldVTableInstance.finish (change fun source => {source with callableSource := source.callableSource.map fun header =>
        {header with container := some "trait"}}) kcfi first slot) "vtable callable trait header inconsistent"
      reject (WorldVTableInstance.finish (change fun source => {source with genericTemplate := source.genericTemplate.map fun template =>
        {template with parameters := template.parameters.push .type}}) kcfi first slot) "vtable callable template generic header mismatch"
      let some byValue := identities[4]? | throw (IO.userError "by-value source method absent")
      let some byValueSlot := (← must (WorldVTableMethods.ownSlots context 100000 2048 reference))[4]?
        | throw (IO.userError "by-value slot absent")
      let badSelf := {context with generic := {context.generic with definitions := context.generic.definitions.map fun source =>
        if source.crateIndex == byValue.crateIndex && source.index == byValue.index then
          {source with callableSource := source.callableSource.map fun header => {header with hasSelf := false}} else source}}
      reject (WorldVTableInstance.finish badSelf kcfi byValue byValueSlot) "vtable callable trait header inconsistent"
      let specialized := {context with traits := {context.traits with traits := context.traits.traits.map fun declaration =>
        if declaration.definition == reference.definition then {declaration with implementations := declaration.implementations.map fun implementation =>
          {implementation with isDefault := true}} else declaration}}
      reject (WorldVTableInstance.ownDeclarations specialized 100000 2048 kcfi reference) "default impl selection requires specialization semantics"

    total := total + actual.size
    IO.println s!"PASS {name}: final source declarations, empty-instance World interning, repeat identity and controls"
  unless total == 20 do throw (IO.userError "final-instance total changed")
  IO.println "PASS 15 source final slots and 5 Virtual postprocessing components; body/ABI/allocation are separate capabilities"
