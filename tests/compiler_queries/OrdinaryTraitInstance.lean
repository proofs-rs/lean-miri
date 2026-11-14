import Miri.Input.Decoder
import Miri.Input.SourceMirCall
open Lean Miri.Input Miri.Interpreter
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)
private def reject (result : Except String α) (expected : String) : IO Unit := do
  match result with
  | .error actual => unless actual == expected do throw (IO.userError s!"wrong ordinary trait residual: {actual}; expected {expected}")
  | .ok _ => throw (IO.userError s!"ordinary trait accepted {expected}")

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected raw source and try_resolve oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with
    compilerPredicates := #[], instances := #[], allocations := #[],
    functionAbis := #[], bodies := #[], bodyRoots := #[], queries := {original.queries with
      functionFacts := ⟨#[],#[],#[]⟩, nativeSignatures := #[],
      runtime := {original.queries.runtime with types := #[], instances := #[], virtualQueries := #[]},
      vtables := #[], instanceAbis := #[], shimAbis := some #[], namedShimAbis := some #[]}}
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let material ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let arena ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] metadata.target.pointerSize.bytes.toNat)
  let instances ← must (InstanceArena.Store.ofSource arena #[])
  let empty := {material with arena,instances}
  let json ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (json.getObjVal? "queries")).getArr?)
  unless rows.size == 2 do throw (IO.userError "ordinary trait oracle coverage changed")
  let mut checks := 0
  for row in rows do
    let identity ← must (GenericMaterialCodec.readDefinition (← must (row.getObjVal? "method")))
    let selected ← must (GenericMaterialCodec.readDefinition (← must (row.getObjVal? "selected")))
    let terms ← must ((← must ((← must (row.getObjVal? "arguments")).getArr?)).mapM (GenericMaterialCodec.readTerm 4096))
    let expectedArguments ← must ((← must ((← must (row.getObjVal? "selected_arguments")).getArr?)).mapM (GenericMaterialCodec.readTerm 4096))
    unless terms.size == 3 && expectedArguments.size == 2 do throw (IO.userError "ordinary trait rebase fixture lost differing prefixes")
    let ((resolved,_),after) ← must ((SourceMirCall.resolveInWorld document
      ⟨SourceCall.functionTerm ⟨identity,terms⟩,#[],⟨0⟩⟩).run empty)
    let .constructed key ← must (after.instances.lookup resolved.instanceId)
      | throw (IO.userError "ordinary trait selected precomputed instance")
    let expectedPhysical ← must (after.arena.definitionRef selected)
    let actualArguments ← must (GenericInstantiationWorld.ofArguments after.arena 4096 key.arguments)
    unless key.kind == .Item expectedPhysical && key.definition == selected && actualArguments == expectedArguments do
      throw (IO.userError "ordinary source impl Item/rebased args differ from rustc try_resolve")
    let (physical,start) ← must ((RuntimeArrayTypes.liftType
      (GenericInstantiationWorld.resolveArguments 4096 terms)).run empty)
    let method ← must (start.arena.definitionRef identity)
    let context := start.metadata.normalizationContext
    let scope ← must (SourceEnvironmentRuntime.lookupDefinitions context.generic.definitions identity)
    let some parent := scope.genericParent | throw (IO.userError "trait parent absent")
    let traitRows := context.traits.traits.filter (·.definition == parent.definition)
    let some traitSource := traitRows[0]? | throw (IO.userError "trait source absent")
    let some implementation := traitSource.implementations[0]? | throw (IO.userError "impl source absent")
    let changeTrait := fun replacement => {start with metadata := {start.metadata with normalizationContext :=
      {context with traits := {context.traits with traits := context.traits.traits.map fun source =>
        if source.definition == traitSource.definition then replacement else source}}}}
    let specialized := changeTrait {traitSource with implementations := #[{implementation with isDefault := true}]}
    reject ((WorldObjectCandidate.resolveOrdinary 100000 4096 method physical).run specialized)
      "ordinary trait specialization requires source ancestry"
    let ambiguous := changeTrait {traitSource with implementations := #[implementation,implementation]}
    reject ((WorldObjectCandidate.resolveOrdinary 100000 4096 method physical).run ambiguous)
      "duplicate raw impl definition"
    let ambiguousMethod := changeTrait {traitSource with implementations := #[{implementation with
      methods := implementation.methods ++ implementation.methods}]}
    reject ((WorldObjectCandidate.resolveOrdinary 100000 4096 method physical).run ambiguousMethod)
      "ordinary trait selected method source ambiguous"
    let inheritedDefault := changeTrait {traitSource with implementations := #[{implementation with
      methods := implementation.methods.filter (·.traitAssociatedDefinition != identity)}]}
    reject ((WorldObjectCandidate.resolveOrdinary 100000 4096 method physical).run inheritedDefault)
      "ordinary trait default method requires source ancestry"
    let wrongMapping := {start with metadata := {start.metadata with normalizationContext := {context with
      generic := {context.generic with definitions := context.generic.definitions.map fun source =>
        if source.crateIndex == selected.crateIndex && source.index == selected.index then
          {source with callableSource := source.callableSource.map fun header => {header with traitItem := some parent.definition}}
        else source}}}}
    reject ((WorldObjectCandidate.resolveOrdinary 100000 4096 method physical).run wrongMapping)
      "ordinary trait selected method canonical owner mismatch"
    let falseWhere := {start with metadata := {start.metadata with normalizationContext := {context with
      generic := {context.generic with definitions := context.generic.definitions.map fun source =>
        if source.crateIndex == implementation.definition.crateIndex && source.index == implementation.definition.index then
          {source with sourceEnvironment := source.sourceEnvironment.map fun scope => {scope with ownPredicates := scope.ownPredicates.push ⟨#[],.equal (.atom .type "uint" "u8") (.atom .type "uint" "u16")⟩}}
        else source}}}}
    reject ((WorldObjectCandidate.resolveOrdinary 100000 4096 method physical).run falseWhere)
      "trait has no applicable source impl"
    checks := checks + 6
  unless checks == 12 do throw (IO.userError "ordinary trait negative count changed")
  IO.println "PASS 2 ordinary source trait Item selections with 3-to-2 argument rebasing; 12 malformed/ambiguous/specialized/default/where negatives"
