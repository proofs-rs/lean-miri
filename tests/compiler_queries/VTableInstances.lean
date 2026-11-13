import Miri.Input.Decoder
import Miri.Input.WorldVTableInstance
import Miri.Input.CompilerVirtualLeaves
import Miri.Input.CompilerInstanceAbi
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
private def access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := ⟨id,fun _ world => world⟩
private def declarationOf (world : RuntimeArrayTypes.World) (id : InstanceId) :
    Except String WorldVTableInstance.Declaration := do
  let key ← CompilerInstance.source world id
  let kind ← match key.kind with
    | .Item _ => pure WorldVTableInstance.Kind.item
    | .Shim (.VTable _) => pure .vtable
    | .Shim (.Reify _ reason) => pure (.reify reason)
    | _ => throw "raw method oracle returned unexpected instance kind"
  pure ⟨kind,key.definition,← GenericInstantiationWorld.ofArguments world.arena 2048 key.arguments⟩
private def runHook (world : RuntimeArrayTypes.World)
    (action : CallM RuntimeArrayTypes.World α) : IO (α × RuntimeArrayTypes.World) := do
  match action.run world with
  | .ok value after => pure (value,after)
  | .error error _ => throw (IO.userError s!"source virtual hook failed: {reprStr error}")
private def rejectHook (world : RuntimeArrayTypes.World)
    (action : CallM RuntimeArrayTypes.World α) : IO Unit := do
  match action.run world with
  | .ok _ _ => throw (IO.userError "source virtual hook accepted negative control")
  | .error (.unsupported _) _ => pure ()
  | .error error _ => throw (IO.userError s!"wrong source virtual hook negative: {reprStr error}")
def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected source and final-instance oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with compilerPredicates := #[], instances := #[], allocations := #[], functionAbis := #[], queries := {original.queries with runtime := {original.queries.runtime with virtualQueries := #[], types := #[], instances := #[]}, vtables := #[], instanceAbis := #[], shimAbis := some #[], namedShimAbis := some #[]}}
  -- No executable root is needed to demand these compiler leaves. Remove body
  -- seeds as well, so preparation cannot retain instance answers through them.
  let prepared ← must (CompilerCallPipeline.prepare (← must (lowerProgram
    {document with bodies := #[], bodyRoots := #[]})))
  let concreteHooks : VirtualCalls.CompilerHooks RuntimeArrayTypes.World Unit :=
    CompilerVirtualLeaves.make prepared access
  let publicHooks := CompilerCallPipeline.compilerHooks prepared access concreteHooks
  let context ← must (AliasRuntime.Context.ofDocument document)
  let some session := document.producer.abiSession | throw (IO.userError "raw sanitizer session missing")
  let kcfi := some (session.sanitizers.contains "kcfi")
  let metadata ← must ((RuntimeMetadata.ofDocument original).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
  let noAnswers := {metadata.source with compilerPredicates := #[], instances := #[], allocations := #[], functionAbis := #[], queries := {metadata.source.queries with runtime := {metadata.source.queries.runtime with virtualQueries := #[], types := #[], instances := #[]}, vtables := #[], instanceAbis := #[], shimAbis := some #[], namedShimAbis := some #[]}}
  let world := {initial with instances := empty,metadata := {metadata with source := noAnswers,normalizationContext := context}}
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (oracle.getObjVal? "queries")).getArr?)
  unless rows.size == 4 do throw (IO.userError "final-instance oracle coverage changed")
  let mut total := 0
  let mut earlyLifetimeChecks := 0
  let mut rawStaticChecks := 0
  let mut rawByValueChecks := 0
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
        let ownCount := template.parameters.size - reference.arguments.size
        let arguments := reference.arguments ++ Array.replicate ownCount (.atom .region "erased" "")
        if signature.inputs[0]? == some (.parameter .type 0) then
          components := components.push (← must (WorldVTableInstance.finish context kcfi identity (.byValueShim ⟨identity,arguments⟩)))
        else
          components := components.push (some (← must (WorldVTableInstance.finishVirtual context kcfi identity arguments)))
      unless components == wanted do throw (IO.userError "Virtual component postprocessing differs from rustc")
      match WorldVTableInstance.ownDeclarations context 100000 2048 kcfi reference with
      | .ok _ => throw (IO.userError "unimplemented object selection unexpectedly succeeded")
      | .error error => unless error.startsWith "dynamic trait goals" do throw (IO.userError s!"wrong dynamic residual: {error}")
      let (arguments,argumentWorld) ← must ((RuntimeArrayTypes.liftType
        (GenericInstantiationWorld.resolveArguments 2048 reference.arguments)).run world)
      for hooks in #[concreteHooks,publicHooks] do
        for identity in identities do
          let method ← must (argumentWorld.arena.definitionRef identity)
          let some scope := context.generic.definitions[method]?.bind (·.sourceEnvironment)
            | throw (IO.userError "dynamic hook method header absent")
          let full := arguments ++ Array.replicate (scope.parameters.size - arguments.size) (.Lifetime .Erased)
          rejectHook argumentWorld (hooks.expectResolveForVTable () method full)
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
    -- Exercise both production assembly paths, not a direct component call.
    for hooks in #[concreteHooks,publicHooks] do
      for ((identity,id),wanted) in (identities.zip instances).zip wanted do
        let method ← must (after.arena.definitionRef identity)
        let (parent,_) ← runHook after (hooks.parentTrait method)
        let (sourceArgs,withArgs) ← must ((RuntimeArrayTypes.liftType
          (GenericInstantiationWorld.resolveArguments 2048 reference.arguments)).run world)
        let some (Miri.MIR.GenericArg.Type concrete) := sourceArgs[0]? | throw (IO.userError "hook concrete Self absent")
        let some definition := context.generic.definitions[method]? | throw (IO.userError "hook method definition absent")
        let some scope := definition.sourceEnvironment | throw (IO.userError "hook source header absent")
        let ownCount := scope.parameters.size - sourceArgs.size
        let ownRegion := if wanted.any (fun value => value.kind == .vtable) then Miri.MIR.Region.Erased else .Static
        let sourceArgs := sourceArgs ++ Array.replicate ownCount (.Lifetime ownRegion)
        let (rebased,rebasedWorld) ← runHook withArgs (hooks.rebaseVirtualArgs sourceArgs parent concrete)
        unless rebased.extract reference.arguments.size rebased.size ==
            sourceArgs.extract reference.arguments.size sourceArgs.size do
          throw (IO.userError "virtual rebasing changed method-own lifetime arguments")
        match id,wanted with
        | some expectedId,some wanted =>
          let (actualId,selectedWorld) ← runHook rebasedWorld (hooks.expectResolveForVTable () method rebased)
          let actualKey ← must (CompilerInstance.source selectedWorld actualId)
          let expectedKey ← must (CompilerInstance.source after expectedId)
          unless actualKey == expectedKey && selectedWorld.instances.count == 1 do
            throw (IO.userError "real hook did not demand a fresh full World instance")
          if ownCount > 0 && wanted.kind != .vtable then
            let erased := rebased.take reference.arguments.size ++ Array.replicate ownCount (.Lifetime .Erased)
            let (erasedId,_) ← runHook selectedWorld (hooks.expectResolveForVTable () method erased)
            unless erasedId == actualId do throw (IO.userError "Static/Erased own lifetime resolution differs")
            earlyLifetimeChecks := earlyLifetimeChecks + 1
          let (again,repeatedWorld) ← runHook selectedWorld (hooks.expectResolveForVTable () method rebased)
          unless again == actualId && repeatedWorld.instances == selectedWorld.instances &&
              repeatedWorld.arena.constructedTypes == selectedWorld.arena.constructedTypes &&
              repeatedWorld.arena.constructedConstants == selectedWorld.arena.constructedConstants &&
              repeatedWorld.bodies == selectedWorld.bodies do
            throw (IO.userError "real hook did not reuse selected identity")
          let (requiresCaller,_) ← runHook selectedWorld (hooks.requiresCallerLocation actualId)
          let expectedCaller ← must (CompilerRuntimeQueries.instanceRequiresCallerLocation
            context.generic.definitions actualKey.kind)
          unless requiresCaller == expectedCaller do throw (IO.userError "hook caller-location differs")
          rejectHook selectedWorld (hooks.expectResolveForVTable () method #[])
          let missing := {selectedWorld with metadata := {selectedWorld.metadata with
            normalizationContext := {context with generic := {context.generic with
              definitions := context.generic.definitions.mapIdx fun index value =>
                if index == method then {value with callableSource := none} else value}}}}
          rejectHook missing (hooks.expectResolveForVTable () method rebased)
          rejectHook missing (hooks.parentTrait method)
          let badSelf := {selectedWorld with metadata := {selectedWorld.metadata with
            normalizationContext := {context with generic := {context.generic with
              definitions := context.generic.definitions.mapIdx fun index value =>
                if index == parent then {value with sourceEnvironment := value.sourceEnvironment.map fun source =>
                  {source with parameters := #[.region] ++ source.parameters.extract 1 source.parameters.size}} else value}}}}
          rejectHook badSelf (hooks.parentTrait method)
          rejectHook badSelf (hooks.rebaseVirtualArgs sourceArgs parent concrete)
          let (virtual,virtualWorld) ← must ((RuntimeArrayTypes.internInstance
            (.Virtual method 0) sourceArgs).run selectedWorld)
          let (_,checkedWorld) ← runHook virtualWorld
            (VirtualCalls.assertConcrete hooks () concrete method virtual actualId)
          match (VirtualCalls.assertConcrete hooks () concrete method virtual virtual).run checkedWorld with
          | .error (.invalidProgram "virtual/concrete compiler instance mismatch") _ => pure ()
          | _ => throw (IO.userError "virtual/concrete mismatch control failed")
          if wanted.kind != .item then
            match (CallResolution.loadedBodyOfInstance prepared.calls actualId).run selectedWorld with
            | .error "constructed shim body is unsupported" => pure ()
            | .error error => throw (IO.userError s!"wrong constructed shim body residual: {error}")
            | .ok _ => throw (IO.userError "constructed shim obtained an unsupported body")
            let abi ← must (CompilerInstanceAbi.prepare selectedWorld.metadata
              {prepared.scopes.program with input := noAnswers})
            match (CompilerInstanceAbi.abiOfInstanceInWorld abi actualId #[]).run selectedWorld with
            | .error error => unless error.endsWith "constructed instance has no imported FnAbi query" do
                throw (IO.userError s!"wrong constructed shim ABI residual: {error}")
            | .ok _ => throw (IO.userError "constructed shim obtained an unsupported ABI")
        | none,none => rejectHook rebasedWorld (hooks.expectResolveForVTable () method rebased)
        | _,_ => throw (IO.userError "hook expected slot mismatch")
    let rawRows ← must ((← must (row.getObjVal? "raw_static")).getArr?)
    for raw in rawRows do
      let identity ← must (GenericMaterialCodec.readDefinition (← must (raw.getObjVal? "method")))
      let arguments ← must ((← must ((← must (raw.getObjVal? "arguments")).getArr?)).mapM (GenericMaterialCodec.readTerm 2048))
      let some rawWanted ← must (expected (← must (raw.getObjVal? "result")))
        | throw (IO.userError "raw static method oracle returned Vacant")
      for hooks in #[concreteHooks,publicHooks] do
        let method ← must (world.arena.definitionRef identity)
        let (args,argumentWorld) ← must ((RuntimeArrayTypes.liftType
          (GenericInstantiationWorld.resolveArguments 2048 arguments)).run world)
        let (id,selectedWorld) ← runHook argumentWorld (hooks.expectResolveForVTable () method args)
        let actual ← must (declarationOf selectedWorld id)
        unless actual == rawWanted do throw (IO.userError "raw static method result differs from rustc")
        if rawWanted.kind == .vtable then
          unless rawWanted.arguments.contains (.atom .region "static" "") do
            throw (IO.userError "raw VTable oracle lacks noncanonical own Static region")
          let erased := {rawWanted with arguments := rawWanted.arguments.map fun term =>
            if term == (.atom .region "static" "") then .atom .region "erased" "" else term}
          unless actual != erased do throw (IO.userError "raw VTable own Static/Erased control collapsed")
          rawByValueChecks := rawByValueChecks + 1
        rawStaticChecks := rawStaticChecks + 1
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
    IO.println s!"PASS {name}: final declarations, both real hook assemblies, fresh demand/reuse, assertConcrete and negative controls"
  unless total == 20 do throw (IO.userError "final-instance total changed")
  unless earlyLifetimeChecks == 4 do throw (IO.userError "early method lifetime hook coverage changed")
  unless rawStaticChecks == 20 && rawByValueChecks == 4 do throw (IO.userError "raw Static method query coverage changed")
  IO.println "PASS 20 separate raw Static method queries, including 4 VTable own-region preservation controls"
  IO.println "PASS 15 source final slots and 5 Virtual postprocessing components; body/ABI/allocation are separate capabilities"
