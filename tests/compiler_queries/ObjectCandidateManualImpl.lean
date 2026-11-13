import Miri.Input.Decoder
import Miri.Input.WorldObjectCandidate
open Lean Miri.Input Miri.Interpreter GenericSubstitution TraitSelection
private def must [ToString ε] (value : Except ε A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError (toString error))
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def changed (world : RuntimeArrayTypes.World) (identity : DefinitionIdentity)
    (implementations : Array Impl) : RuntimeArrayTypes.World :=
  let context := world.metadata.normalizationContext
  {world with metadata := {world.metadata with normalizationContext :=
    {context with traits := {context.traits with traits := context.traits.traits.map fun declaration =>
      if declaration.definition == identity then {declaration with implementations} else declaration}}}}
private def reject (world : RuntimeArrayTypes.World) (method : Miri.MIR.DefId)
    (arguments : Array Miri.MIR.GenericArg) (expected : String) : IO Unit := do
  match (WorldObjectCandidate.select 100000 4096 method arguments).run world with
  | .error error => check (error == expected) s!"wrong catalog error: {error}; expected {expected}"
  | .ok _ => throw (IO.userError s!"unsupported impl catalog accepted: {expected}")

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected actual runtime source and compiler oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with
    compilerPredicates := #[],instances := #[],allocations := #[],
    functionAbis := #[],bodies := #[],bodyRoots := #[],queries := {original.queries with
      functionFacts := ⟨#[],#[],#[]⟩,nativeSignatures := #[],
      runtime := {original.queries.runtime with types := #[],instances := #[],virtualQueries := #[]},
      vtables := #[],instanceAbis := #[],shimAbis := some #[],namedShimAbis := some #[]}}
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let material ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let arena ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] metadata.target.pointerSize.bytes.toNat)
  let instances ← must (InstanceArena.Store.ofSource arena #[])
  let empty := {material with arena,instances}
  let json ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (json.getObjVal? "queries")).getArr?)
  let mut total := 0
  for row in rows do
    let methods ← must ((← must (row.getObjVal? "methods")).getArr?)
    for method in methods do
      let identity ← must (GenericMaterialCodec.readDefinition (← must (method.getObjVal? "method")))
      let physical ← must (arena.definitionRef identity)
      let terms ← must ((← must ((← must (method.getObjVal? "arguments")).getArr?)).mapM (GenericMaterialCodec.readTerm 4096))
      let (arguments,start) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveArguments 4096 terms)).run empty)
      let some (Miri.MIR.GenericArg.Type owner) := arguments[0]? | throw (IO.userError "Self absent")
      let (some view,_) ← must ((WorldDynamicData.query 4096 owner).run start) | throw (IO.userError "dynamic absent")
      let (principal,_) ← must ((WorldDynamicData.principalRef 4096 view).run start)
      let declarations := start.metadata.normalizationContext.traits.traits.filter (·.definition == principal.definition)
      let some declaration := declarations[0]? | throw (IO.userError "trait source absent")
      check (declarations.size == 1 && declaration.implementations.size == 1) "actual Value Cell impl catalog changed"
      let some implementation := declaration.implementations[0]? | throw (IO.userError "raw Cell impl absent")
      let some (GenericSubstitution.Term.definition .type "adt" _ _) := implementation.traitRef.arguments[0]?
        | throw (IO.userError "actual impl Self is not raw Cell ADT")
      let (selected,after) ← must ((WorldObjectCandidate.resolveOrdinary 100000 4096 physical arguments).run start)
      let .constructed key ← must (after.instances.lookup selected) | throw (IO.userError "copied ordinary instance")
      let expected ← must (method.getObjVal? "ordinary")
      let slot ← must ((← must (expected.getObjVal? "slot")).getNat?)
      check (key.kind == .Virtual physical slot && key.arguments == arguments) "actual manual-catalog Virtual differs from rustc try_resolve"
      check (after.arena.materialTypes.isEmpty && after.instances.material.isEmpty) "candidate acquired material answer prefix"
      let (reified,finished) ← must ((WorldObjectCandidate.resolveForVTable 100000 4096 physical arguments).run start)
      let .constructed reify ← must (finished.instances.lookup reified) | throw (IO.userError "copied reify instance")
      let expectedKind ← must ((← must ((← must (method.getObjVal? "vtable")).getObjVal? "kind")).getStr?)
      let reason := if expectedKind == "reify_vtable" then some CallReifyReason.Vtable else none
      check ((expectedKind == "reify_vtable" || expectedKind == "reify_none") &&
        reify.kind == .Shim (.Reify physical reason) && reify.arguments == arguments)
        "manual-catalog Reify differs from rustc vtable resolution"
      let cases : Array (Impl × String) := #[
        ({implementation with isDefault := true},"object candidate specialization requires source ordering"),
        ({implementation with methods := implementation.methods.map fun entry => {entry with isFinal := false}},"object candidate specialization requires source ordering"),
        ({implementation with parameters := #[.type]},"object candidate impl canonical source scope mismatch"),
        ({implementation with traitRef := {implementation.traitRef with definition := ⟨999,999⟩}},"object candidate impl belongs to another trait source"),
        ({implementation with traitRef := {implementation.traitRef with arguments := #[]}},"object candidate impl trait argument arity mismatch"),
        ({implementation with traitRef := {implementation.traitRef with arguments := #[.atom .region "static" ""]}},"object candidate impl trait argument sort mismatch"),
        ({implementation with traitRef := {implementation.traitRef with arguments := #[view.source]}},"dynamic impl relevance requires principal trait classification"),
        ({implementation with traitRef := {implementation.traitRef with arguments := #[.definition .type "alias_projection_not_rigid" identity .nil]}},"object candidate competing impls require candidate winnowing"),
        ({implementation with traitRef := {implementation.traitRef with arguments := #[.atom .type "unknown_head" ""]}},"unknown generic syntax primitive type")]
      for (candidate,expectedError) in cases do
        reject (changed start principal.definition #[candidate]) physical arguments expectedError
      reject (changed start principal.definition #[implementation,implementation]) physical arguments
        "object candidate duplicate raw impl definition"
      let blanket := {implementation with parameters := #[.type],traitRef := {implementation.traitRef with arguments := #[.parameter .type 0]}}
      let blanketState := changed start principal.definition #[blanket]
      let context := blanketState.metadata.normalizationContext
      let definitionRef ← must (GenericInstantiation.definitionRef context.generic implementation.definition)
      let some raw := context.generic.definitions[definitionRef]? | throw (IO.userError "impl raw definition absent")
      let some scope := raw.sourceEnvironment | throw (IO.userError "impl raw scope absent")
      let definitions := context.generic.definitions.set! definitionRef {raw with sourceEnvironment := some {scope with parameters := #[.type]}}
      let blanketState := {blanketState with metadata := {blanketState.metadata with normalizationContext :=
        {context with generic := {context.generic with definitions}}}}
      reject blanketState physical arguments "object candidate competing impls require candidate winnowing"
      total := total+1
  check (total == 2) "expected actual get/set Virtual methods"
  IO.println "PASS2 actual Value/Cell Virtual+Reify selections vs rustc try_resolve;22 raw-catalog negatives;empty type/instance prefixes"
