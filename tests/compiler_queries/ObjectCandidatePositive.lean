import Miri.Input.Decoder
import Miri.Input.WorldObjectCandidate
import Miri.Input.SourceMirCall
open Lean Miri.Input Miri.Interpreter
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error e => throw (IO.userError e)

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected source and genuine oracle")
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
  let mut positives := 0
  let mut residuals := 0
  for row in rows do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let methods ← must ((← must (row.getObjVal? "methods")).getArr?)
    for method in methods do
      let identity ← must (GenericMaterialCodec.readDefinition (← must (method.getObjVal? "method")))
      let physical ← must (empty.arena.definitionRef identity)
      let terms ← must ((← must ((← must (method.getObjVal? "arguments")).getArr?)).mapM (GenericMaterialCodec.readTerm 4096))
      let (arguments,start) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveArguments 4096 terms)).run empty)
      if #["query_base","query_generic","query_auto","query_lifetime"].contains name then
        let ((resolved,_),after) ← must ((SourceMirCall.resolveInWorld document
          ⟨SourceCall.functionTerm ⟨identity,terms⟩,#[],⟨0⟩⟩).run start)
        let ordinary := resolved.instanceId
        let .constructed key ← must (after.instances.lookup ordinary) | throw (IO.userError "ordinary reused compiler answer")
        let expected ← must (method.getObjVal? "ordinary")
        let expectedSlot ← must ((← must (expected.getObjVal? "slot")).getNat?)
        unless key.kind == .Virtual physical expectedSlot && key.arguments == arguments do
          throw (IO.userError "source Virtual differs from genuine rustc oracle")
        let (reified,finished) ← must ((WorldObjectCandidate.resolveForVTable 100000 4096 physical arguments).run start)
        let .constructed reify ← must (finished.instances.lookup reified) | throw (IO.userError "reify reused compiler answer")
        let expectedKind ← must ((← must ((← must (method.getObjVal? "vtable")).getObjVal? "kind")).getStr?)
        let reason := if expectedKind == "reify_vtable" then some CallReifyReason.Vtable else none
        unless (expectedKind == "reify_vtable" || expectedKind == "reify_none") &&
            reify.kind == .Shim (.Reify physical reason) && reify.arguments == arguments do
          throw (IO.userError "source Reify differs from genuine rustc oracle")
        let (concreteSelf,concreteWorld) ← must ((RuntimeArrayTypes.liftType
          (GenericInstantiationWorld.resolveType 4096 (.atom .type "uint" "u8"))).run start)
        match (WorldObjectCandidate.resolveOrdinary 100000 4096 physical
            (arguments.set! 0 (.Type concreteSelf))).run concreteWorld with
        | .error "trait has no applicable source impl" => pure ()
        | _ => throw (IO.userError "concrete trait Self fabricated an Item instance")
        match (WorldObjectCandidate.resolveOrdinary 100000 4096 physical #[]).run start with
        | .error "ordinary trait method canonical Self absent" => pure ()
        | _ => throw (IO.userError "trait method without Self fabricated an Item instance")
        -- A duplicate source catalog is ambiguity, never successful selection.
        let some (Miri.MIR.GenericArg.Type owner) := arguments[0]? | throw (IO.userError "Self absent")
        let (some view,_) ← must ((WorldDynamicData.query 4096 owner).run start) | throw (IO.userError "dyn absent")
        let (principal,_) ← must ((WorldDynamicData.principalRef 4096 view).run start)
        let context := start.metadata.normalizationContext
        let source := context.traits.traits.filter (·.definition == principal.definition)
        let ambiguous := {start with metadata := {start.metadata with normalizationContext :=
          {context with traits := {context.traits with traits := context.traits.traits ++ source}}}}
        match (WorldObjectCandidate.select 100000 4096 physical arguments).run ambiguous with
        | .error "dynamic predicate trait source missing or ambiguous" => pure ()
        | .error actual => throw (IO.userError s!"wrong ambiguous source residual: {actual}")
        | .ok _ => throw (IO.userError "ambiguous raw source selected an object")
        let defaultImpl : TraitSelection.Impl := {
          definition := principal.definition, parameters := #[], traitRef := principal,
          polarity := .positive, isDefault := true, associatedValues := #[]}
        let specialized := {start with metadata := {start.metadata with normalizationContext :=
          {context with traits := {context.traits with traits := context.traits.traits.map fun trait =>
            if trait.definition == principal.definition then
              {trait with implementations := #[defaultImpl]} else trait}}}}
        match (WorldObjectCandidate.select 100000 4096 physical arguments).run specialized with
        | .error "object candidate specialization requires source ordering" => pure ()
        | _ => throw (IO.userError "specialized source selected without ordering")
        -- Generic principal arguments must match, beyond trait identity.
        if name == "query_generic" then
          let (wrongType,badWorld) ← must ((RuntimeArrayTypes.liftType
            (GenericInstantiationWorld.resolveType 4096 (.atom .type "uint" "u16"))).run start)
          let malformed := arguments.set! 1 (.Type wrongType)
          match (WorldObjectCandidate.select 100000 4096 physical malformed).run badWorld with
          | .error "object candidate trait arguments do not match principal" => pure ()
          | _ => throw (IO.userError "mismatched generic principal selected an object")
        positives := positives + 1
      else
        match (WorldObjectCandidate.select 100000 4096 physical arguments).run start with
        | .error reason =>
          unless #["object candidate higher-ranked relation requires universe provider",
            "object candidate projection obligations require source confirmation",
            "object candidate explicit supertrait requires source confirmation",
            "object candidate upcast requires supertrait confirmation"].contains reason do
            throw (IO.userError s!"unexpected object candidate residual: {reason}")
        | .ok _ => throw (IO.userError "unsupported object candidate unexpectedly selected")
        residuals := residuals + 1
  unless positives == 4 && residuals == 11 do throw (IO.userError "object slice source coverage changed")
  IO.println "PASS 4 source Virtual +4 Reify; 4 concrete Self +4 absent Self rejects; 4 ambiguous catalogs; 4 specialization guards; 1 generic mismatch; 11 explicit residuals"
