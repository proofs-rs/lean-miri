import Miri.Input.Decoder
import Miri.Input.WorldDynamicData
import Miri.Input.RawFunctionSignature
import Miri.Input.CompilerVTableLeaves
open Lean Miri.Input GenericSubstitution Miri.Interpreter Miri.Memory Miri.ABI
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def reject (result : Except String α) (message : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"typed bridge accepted {message}")
  | .error actual => unless actual == message do throw (IO.userError s!"wrong typed bridge residual: {actual}")


private def eraseOpened : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0,_ => throw "source query region opening exhausted"
  | fuel+1,term => match term with
    | .placeholder .region 1 _ _ => pure (.atom .region "erased" "")
    | .binder variables body => return .binder variables (← eraseOpened fuel body)
    | .node sort tag payload children => return .node sort tag payload (← children.mapM (eraseOpened fuel))
    | .definition sort tag definition children => return .definition sort tag definition (← children.mapM (eraseOpened fuel))
    | _ => pure term

structure Probe where
  world : RuntimeArrayTypes.World
  functions : FunctionPointers.Registry Unit := .empty
  vtables : VTableMachine.Registry := .empty
private abbrev State := MachineHooks.State Unit Probe
private def access : RuntimeArrayQueries.Access State := {
  get := fun state => state.machine.user.world
  set := fun state world => {state with machine := {state.machine with user := {state.machine.user with world}}} }
private def state (world : RuntimeArrayTypes.World) : State := {
  stack := .empty
  machine := {
    memory := MemoryState.empty, borrowTracker := none, dataRace := none,
    threads := Miri.Concurrency.ThreadManager.initial false, raceAllocations := #[], allocationSpans := #[],
    user := ⟨world,.empty,.empty⟩} }
private def failLeaf : MachineHooks.M Unit Probe α := throw (.unsupported "unreached physical dynamic-data check leaf")
private def engine (target : RuntimeTargetDataLayout) : VTableMachine.Hooks Unit Probe Unit := {
  functions := {
    registry := (·.functions),putRegistry := fun user functions => {user with functions},
    crossCrateInlineAlways := false, instanceArgs := fun _ => failLeaf,inlineNever := fun _ => failLeaf,
    chooseSalt := pure ⟨0,by decide⟩,ptrGetAlloc := fun _ => failLeaf,
    adjustRootPointer := fun _ _ => failLeaf,importedFunction := fun _ => failLeaf}
  registry := (·.vtables),putRegistry := fun user vtables => {user with vtables},target,
  importedVTable := fun _ => failLeaf }
private def runStep (before : State) (action : CallM State α) : IO (α × State) := do
  match action.run before with
  | .ok result after => pure (result,after)
  | .error error _ => throw (IO.userError s!"dynamic runtime callback failed: {reprStr error}")
private def rejectStep (before : State) (action : CallM State α) (reason : String) : IO Unit := do
  match action.run before with
  | .error (.unsupported actual) after =>
    unless actual.endsWith reason do throw (IO.userError s!"wrong dynamic callback residual: {actual}; wanted {reason}")
    unless after.machine.memory.nextAllocId == before.machine.memory.nextAllocId &&
        after.machine.user.vtables.entries.size == before.machine.user.vtables.entries.size &&
        after.machine.user.world.arena.constructedPredicates == before.machine.user.world.arena.constructedPredicates do
      throw (IO.userError "unsupported dynamic callback allocated or changed predicate identities")
  | .error error _ => throw (IO.userError s!"wrong dynamic callback failure: {reprStr error}")
  | .ok _ _ => throw (IO.userError "unported dynamic callback succeeded")

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected genuine source and matching dynamic oracle")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with
    compilerPredicates := #[], instances := #[], allocations := #[],
    functionAbis := #[], bodies := #[], bodyRoots := #[], queries := {original.queries with
      functionFacts := ⟨#[],#[],#[]⟩,nativeSignatures := #[],
      runtime := {original.queries.runtime with types := #[], instances := #[], virtualQueries := #[]},
      vtables := #[], instanceAbis := #[], shimAbis := some #[], namedShimAbis := some #[]}}
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let material ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let emptyArena ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] metadata.target.pointerSize.bytes.toNat)
  let emptyInstances ← must (InstanceArena.Store.ofSource emptyArena #[])
  let empty := {material with arena := emptyArena,instances := emptyInstances}
  let providers ← must (CompilerProviders.prepare (← must (lowerProgram document)))
  let calls := providers.lifecycle.calls
  let compiler : VirtualCalls.CompilerHooks State Unit := CompilerVirtualLeaves.make calls access
  let compilers := #[compiler,CompilerCallPipeline.compilerHooks calls access compiler]
  let image := AllocationImage.Imported.ofSource #[] #[]
  let machine := engine metadata.target
  let concrete : VTableHooks Provenance State Unit CallInstance (FnAbi Miri.MIR.TyId) :=
    CompilerVTableLeaves.make providers access image machine (fun _ _ _ _ _ => failLeaf)
  let tables := #[concrete,
    CompilerVTableMachine.vtableHooks providers.vtables access image machine concrete,
    CompilerCallPipeline.vtableHooks calls access image (fun state => state.machine.memory) concrete]
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (oracle.getObjVal? "queries")).getArr?)
  unless rows.size == 9 do throw (IO.userError "typed dynamic oracle coverage changed")
  let mut materialCount := 0
  let mut prefixReuseChecks := 0
  for node in document.types do
    if let .dynamicTraitObject .. := node.shape then
      let some view ← must ((WorldDynamicData.ofWorld 4096 material.arena node.id).mapError fun e => s!"material view {node.id}: {e}")
        | throw (IO.userError "material dynamic source was lost")
      let some (.dynamic expected) ← must (material.arena.materialKey node)
        | throw (IO.userError "material dynamic has no raw source key")
      unless view.value == expected do throw (IO.userError "material predicate-ID decoding differs")
      let .dynamicTraitObject expectedPredicates expectedPrincipal _ := node.shape
        | throw (IO.userError "material dynamic kind changed")
      for hooks in compilers do
        let (some data,after) ← runStep (state material) (hooks.dynamicData node.id)
          | throw (IO.userError "material runtime Dynamic callback lost its source")
        unless data.predicates == expectedPredicates && data.principal == expectedPrincipal &&
            after.machine.user.world.arena.constructedPredicates.isEmpty do
          throw (IO.userError "material runtime predicate prefix changed")
      if prefixReuseChecks == 0 then
        let novel := {view.value with region := if view.value.region == .Static then .Erased else .Static}
        let (newOwner,newWorld) ← must ((RuntimeArrayTypes.liftType (TypeArena.World.internType (.dynamic novel))).run material)
        let .constructed (.dynamic _) ← must (newWorld.arena.lookupType newOwner)
          | throw (IO.userError "material predicate reuse control did not construct a new dyn owner")
        for hooks in compilers do
          let (some data,after) ← runStep (state newWorld) (hooks.dynamicData newOwner)
            | throw (IO.userError "new owner lost its material predicate reuse")
          unless data.predicates == expectedPredicates && data.principal == expectedPrincipal &&
              after.machine.user.world.arena.constructedPredicates.isEmpty do
            throw (IO.userError "new owner did not reuse immutable material predicate handles")
          prefixReuseChecks := prefixReuseChecks + 1
      materialCount := materialCount + 1
  unless materialCount > 0 do throw (IO.userError "no actual material Dynamic controls")
  let mut quantified := 0
  let mut projectionRows := 0
  let mut principalAbsent := 0
  let mut staleBranchChecks := 0
  let mut runtimeCallbacks := 0
  let mut guardChecks := 0
  let mut confirmationNegatives := 0
  let mut confirmationPositives := 0
  let mut binderConfirmationNegatives := 0
  let mut declarationNegatives := 0
  let mut constTagChecks := 0
  let mut prefixReinterpretationNegatives := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "dynamic")))
    let queryIdentity ← must (GenericMaterialCodec.readDefinition (← must (row.getObjVal? "query_definition")))
    let queryIndex ← must (GenericInstantiation.definitionRef metadata.normalizationContext.generic queryIdentity)
    let some template := document.definitions[queryIndex]?.bind (·.genericTemplate)
      | throw (IO.userError "source query declaration template absent")
    let some signature := template.signatureExpression | throw (IO.userError "source query raw signature absent")
    let signature ← must (RawFunctionSignature.read signature)
    unless BinderRegions.regionOnly signature.variables do throw (IO.userError "source query has non-region binder")
    let some input := signature.inputs[0]? | throw (IO.userError "source query argument absent")
    let opened ← must (TraitSelection.Universes.openTerm signature.variables 1 4096 0 input)
    let erased ← must (eraseOpened 4096 opened)
    let .node .type "reference" _ (.cons _ (.cons sourceDynamic .nil)) := erased
      | throw (IO.userError "source query argument is not a reference")
    unless sourceDynamic == term do throw (IO.userError "typed Dynamic oracle differs from raw source declaration")
    let (owner,world) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 4096 term)).run empty)
    let .constructed (.dynamic _) ← must (world.arena.lookupType owner)
      | throw (IO.userError "empty-prefix Dynamic reused a material identity")
    let (some view,after) ← must (((WorldDynamicData.query 4096 owner).run world).mapError fun e => s!"constructed view: {e}")
      | throw (IO.userError "new Dynamic source bridge returned none")
    unless view.owner == owner && view.source == term do throw (IO.userError "typed owner/source mismatch")
    let written ← must (DynamicPredicate.writeDynamic
      (GenericInstantiationWorld.ofArgument after.arena 4096)
      (GenericInstantiationWorld.ofRegion after.arena) view.value)
    unless written == term do throw (IO.userError "typed dynamic syntax roundtrip differs from rustc")
    unless after.arena.constructedTypes == world.arena.constructedTypes &&
        after.arena.constructedConstants == world.arena.constructedConstants &&
        after.instances == world.instances && after.bodies == world.bodies do
      throw (IO.userError "typed Dynamic read mutated execution stores")
    let (again,repeated) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 4096 term)).run after)
    unless again == owner && repeated.arena.constructedTypes == after.arena.constructedTypes &&
        repeated.arena.constructedConstants == after.arena.constructedConstants do
      throw (IO.userError "typed Dynamic did not reuse current-World identity")
    let _ ← must ((WorldDynamicData.validate 4096 view).run repeated)
    let (.dynamic validityPredicates,validityWorld) ← must
      ((CompilerFactAdapters.validityKindInWorld calls.symbols.facts owner).run world.arena)
      | throw (IO.userError "constructed validity classifier lost Dynamic")
    let (some validityData,validityRepeat) ← must
      ((WorldDynamicSource.runtimeData metadata 4096 owner).run validityWorld)
      | throw (IO.userError "shared World source callback lost Dynamic")
    unless validityPredicates == validityData.predicates &&
        validityWorld.constructedPredicates == validityRepeat.constructedPredicates &&
        validityWorld.materialPredicates.isEmpty &&
        validityPredicates == Array.range view.value.predicates.size do
      throw (IO.userError "validity/source predicate handles did not commit/reuse one execution suffix")
    if let some principal := validityData.principal then
      let .trait .. := (← must (validityRepeat.existential principal)).body
        | throw (IO.userError "validity principal is not an actual trait predicate")
    for hooks in compilers do
      let start := state world
      let (some data,selected) ← runStep start (hooks.dynamicData owner)
        | throw (IO.userError "constructed runtime Dynamic callback returned none")
      let selectedWorld := selected.machine.user.world
      unless selectedWorld.arena.materialPredicates.isEmpty &&
          data.predicates == Array.range view.value.predicates.size &&
          selectedWorld.arena.constructedPredicates == view.value.predicates do
        throw (IO.userError "runtime predicate suffix is not checked dense ordered source data")
      let typed ← must (data.predicates.mapM selectedWorld.arena.existential)
      unless typed == view.value.predicates do throw (IO.userError "runtime handles differ from rustc predicates")
      let principal ← must (data.principal.mapM selectedWorld.arena.existential)
      unless principal == view.principal do throw (IO.userError "runtime principal handle differs from rustc")
      let (definition,_) ← must ((WorldDynamicData.principalDefinition 4096 view).run selectedWorld)
      match definition,view.principal with
      | some definition,some predicate =>
        unless (← must (selectedWorld.arena.identity definition)) == predicate.body.definition do
          throw (IO.userError "principal predicate handle was confused with a physical definition")
      | none,none => pure ()
      | _,_ => throw (IO.userError "principal physical conversion lost None state")
      let (some again,againState) ← runStep selected (hooks.dynamicData owner)
        | throw (IO.userError "repeated runtime callback returned none")
      unless again.predicates == data.predicates && again.principal == data.principal &&
          againState.machine.user.world.arena.constructedPredicates == selectedWorld.arena.constructedPredicates &&
          againState.machine.user.world.arena.constructedTypes == selectedWorld.arena.constructedTypes &&
          againState.machine.user.world.arena.constructedConstants == selectedWorld.arena.constructedConstants do
        throw (IO.userError "runtime predicate callback failed stable World reuse")
      reject (selectedWorld.arena.existential selectedWorld.arena.predicateCount)
        "dynamic constructed predicate is absent"
      let methods ← must ((← must (row.getObjVal? "methods")).getArr?)
      for method in methods do
        let physical ← must (GenericMaterialCodec.readDefinition (← must (method.getObjVal? "method")))
        let definition ← must (selectedWorld.arena.definitionRef physical)
        let terms ← must ((← must ((← must (method.getObjVal? "arguments")).getArr?)).mapM (GenericMaterialCodec.readTerm 4096))
        let (arguments,callWorld) ← must ((RuntimeArrayTypes.liftType
          (GenericInstantiationWorld.resolveArguments 4096 terms)).run selectedWorld)
        let name ← must ((← must (row.getObjVal? "name")).getStr?)
        match (hooks.expectResolveForVTable () definition arguments).run (state callWorld) with
        | .error (.unsupported reason) _ =>
          if reason.endsWith "object candidate higher-ranked relation requires universe provider" &&
              view.value.predicates.any (fun predicate => !predicate.variables.isEmpty) then
            binderConfirmationNegatives := binderConfirmationNegatives + 1
          else unless #["object candidate projection obligations require source confirmation",
              "object candidate explicit supertrait requires source confirmation",
              "object candidate upcast requires supertrait confirmation"].any (fun residual => reason.endsWith residual) do
            throw (IO.userError s!"wrong object confirmation residual: {reason}")
          unless !#["query_base","query_auto","query_lifetime"].contains name do
            throw (IO.userError "covered direct-principal hook rejected source selection")
          confirmationNegatives := confirmationNegatives + 1
        | .ok result afterCall =>
          unless #["query_base","query_auto","query_lifetime"].contains name do
            throw (IO.userError "unsupported object candidate selected an instance")
          let .constructed actual ← must (afterCall.machine.user.world.instances.lookup result)
            | throw (IO.userError "object hook reused compiler instance material")
          let expected ← must (method.getObjVal? "vtable")
          let expectedKind ← must ((← must (expected.getObjVal? "kind")).getStr?)
          let reason := if expectedKind == "reify_vtable" then some CallReifyReason.Vtable else none
          unless (expectedKind == "reify_vtable" || expectedKind == "reify_none") &&
              actual.kind == .Shim (.Reify definition reason) && actual.arguments == arguments do
            throw (IO.userError "actual runtime object hook differs from genuine Reify oracle")
          confirmationPositives := confirmationPositives + 1
        | .error error _ => throw (IO.userError s!"wrong object callback failure: {reprStr error}")
      if projectionRows == 0 && view.value.predicates.any (fun p => match p.body with | .projection .. => true | _ => false) then
        let some first := data.predicates[0]? | throw (IO.userError "suffix guard input absent")
        unless first < providers.program.input.predicates.size do
          throw (IO.userError "suffix/prepared-material-prefix collision control changed")
        let some rawDynamic := document.types.find? (fun node => match node.shape with | .dynamicTraitObject .. => true | _ => false)
          | throw (IO.userError "material codec guard input absent")
        reject (selectedWorld.arena.materialKey {rawDynamic with shape := .dynamicTraitObject data.predicates data.principal .Erased})
          "material dynamic type references a constructed predicate handle"
        reject (selectedWorld.arena.materialKey {rawDynamic with shape := .dynamicTraitObject #[] data.principal .Erased})
          "material dynamic principal references a constructed predicate handle"
        prefixReinterpretationNegatives := prefixReinterpretationNegatives + 2
        for table in tables do
          let reason := "constructed runtime predicate requires source vtable comparison/normalization/allocation"
          rejectStep selected (table.predicates () data.predicates) reason
          rejectStep selected (table.normalizePredicate () ⟨first,0,false⟩) reason
          rejectStep selected (table.ensureMonomorphicDyn () data.predicates) reason
          rejectStep selected (table.reserveVTable () 0 data.predicates 0) reason
          rejectStep selected (table.eraseAndAnonymize () 0 data.predicates) "constructed type requires source vtable query"
          rejectStep selected (table.ensureMonomorphicType () 0) "constructed type requires source vtable query"
          rejectStep selected (table.entries () data.principal 0) "constructed type requires source vtable query"
          guardChecks := guardChecks + 7
        -- The underlying existing machine allocator really can reserve keys in
        -- this inactive raw-AllocId profile. Final assemblies must guard first.
        let (_,baseline) ← runStep selected (VTableMachine.reserve machine 0 #[] ⟨0,by decide⟩)
        unless baseline.machine.memory.nextAllocId != selected.machine.memory.nextAllocId do
          throw (IO.userError "allocation guard baseline no longer exercises a real reserve")
      runtimeCallbacks := runtimeCallbacks + 1
    if view.value.predicates.any (fun predicate => !predicate.variables.isEmpty) then quantified := quantified + 1
    if view.principal.isNone then
      principalAbsent := principalAbsent + 1
      reject ((WorldDynamicData.principalRef 4096 view).run after) "object method candidate requires a principal"
    else
      let (reference,_) ← must ((WorldDynamicData.principalRef 4096 view).run after)
      unless reference.arguments[0]? == some term do throw (IO.userError "principal attached another Self")
      let some originalPrincipal := view.principal | throw (IO.userError "principal view disappeared")
      let duplicate := {view.value with predicates := view.value.predicates ++ #[originalPrincipal]}
      -- Put duplicate principals adjacent, preserving source rank order, so
      -- the actual runtime principal-count guard must reject the malformed key.
      let duplicate := {duplicate with predicates := duplicate.predicates.filter (fun p => match p.body with | .trait .. => true | _ => false)}
      let (duplicateOwner,duplicateWorld) ← must ((RuntimeArrayTypes.liftType
        (TypeArena.World.internType (.dynamic duplicate))).run after)
      let wrongKind := {view.value with predicates := view.value.predicates.map fun predicate =>
        match predicate.body with
        | .trait _ arguments => {predicate with body := .trait queryIdentity arguments}
        | _ => predicate}
      let (wrongOwner,wrongWorld) ← must ((RuntimeArrayTypes.liftType
        (TypeArena.World.internType (.dynamic wrongKind))).run after)
      let some principal := view.principal | throw (IO.userError "principal view disappeared")
      let context := after.metadata.normalizationContext
      let missing := {after with metadata := {after.metadata with normalizationContext := {context with
        traits := {context.traits with traits := context.traits.traits.filter (·.definition != principal.body.definition)}}}}
      for hooks in compilers do
        rejectStep (state duplicateWorld) (hooks.dynamicData duplicateOwner)
          "typed dynamic runtime bridge: multiple principals"
        rejectStep (state wrongWorld) (hooks.dynamicData wrongOwner)
          "dynamic predicate trait source missing or ambiguous"
        rejectStep (state missing) (hooks.dynamicData owner)
          "dynamic predicate trait source missing or ambiguous"
        declarationNegatives := declarationNegatives + 3
    if view.value.predicates.any (fun predicate => match predicate.body with | .projection .. => true | _ => false) then
      projectionRows := projectionRows + 1
      let some projection := view.value.predicates.find? (fun p => match p.body with | .projection .. => true | _ => false)
        | throw (IO.userError "projection row lost its projection")
      let .projection associated arguments (.type projectedType) := projection.body
        | throw (IO.userError "actual compiler projection is not Type")
      let (constant,withConstant) ← must ((RuntimeArrayTypes.liftType (TypeArena.World.internConstant
        (.Value projectedType ⟨#[.Leaf 7 1],0⟩))).run after)
      let constPredicate := {projection with body := .projection associated arguments (.constant constant)}
      let (typeHandle,typeArena) ← must ((TypeArena.World.internExistential projection).run withConstant.arena)
      let (constHandle,constArena) ← must ((TypeArena.World.internExistential constPredicate).run typeArena)
      unless typeHandle != constHandle && (← must (constArena.existential constHandle)) == constPredicate do
        throw (IO.userError "predicate syntax arena conflated Type and Const projection terms")
      constTagChecks := constTagChecks + 1
      let constDynamic := {view.value with predicates := view.value.predicates.map fun p =>
        if p == projection then constPredicate else p}
      let (constOwner,constWorld) ← must ((RuntimeArrayTypes.liftType
        (TypeArena.World.internType (.dynamic constDynamic))).run withConstant)
      let context := after.metadata.normalizationContext
      let missingScope := {after with metadata := {after.metadata with normalizationContext := {context with generic :=
        {context.generic with definitions := context.generic.definitions.map fun definition =>
          if definition.crateIndex == associated.crateIndex && definition.index == associated.index then
            {definition with sourceEnvironment := none} else definition}}}}
      for hooks in compilers do
        rejectStep (state constWorld) (hooks.dynamicData constOwner)
          "dynamic projection term kind disagrees with source declaration"
        rejectStep (state missingScope) (hooks.dynamicData owner)
          "raw source environment declaration is absent"
        declarationNegatives := declarationNegatives + 2
      -- This actual corpus row has one u8 projection child at id0 and dyn owner1.
      -- Create a sibling branch where child0 is i16 but the dyn payload IDs are
      -- identical. The cached source term, not numeric payload equality, must
      -- reject cross-branch reuse.
      let (wrongChild,branch) ← must ((RuntimeArrayTypes.liftType
        (TypeArena.World.internType (.integer true .i16))).run empty)
      unless wrongChild == 0 do throw (IO.userError "sibling branch control child changed")
      let (wrongOwner,branch) ← must ((RuntimeArrayTypes.liftType
        (TypeArena.World.internType (.dynamic view.value))).run branch)
      unless wrongOwner == owner do throw (IO.userError "sibling branch owner collision control changed")
      let some other ← must (WorldDynamicData.ofWorld 4096 branch.arena wrongOwner)
        | throw (IO.userError "sibling branch dynamic source absent")
      unless other.value == view.value && other.source != view.source do
        throw (IO.userError "sibling branch control lacks numeric-payload collision")
      reject ((WorldDynamicData.validate 4096 view).run branch)
        "typed dynamic runtime bridge: owner/payload differs from current World"
      staleBranchChecks := staleBranchChecks + 1
    if view.principal.isSome then
      let malformed := {view.value with predicates := view.value.predicates.mapIdx fun index predicate =>
        if index == 0 then {predicate with variables := #[.type .anonymous]} else predicate}
      let (badOwner,badWorld) ← must ((RuntimeArrayTypes.liftType (TypeArena.World.internType (.dynamic malformed))).run after)
      reject (WorldDynamicData.ofWorld 4096 badWorld.arena badOwner)
        "typed dynamic runtime bridge: non-region existential binder unsupported"
      for hooks in compilers do
        rejectStep (state badWorld) (hooks.dynamicData badOwner)
          "typed dynamic runtime bridge: non-region existential binder unsupported"
        declarationNegatives := declarationNegatives + 1
  unless quantified == 1 && projectionRows == 2 && principalAbsent == 1 && staleBranchChecks == 2 do
    throw (IO.userError "typed bridge binder/projection/owner control counts changed")
  unless binderConfirmationNegatives == 2 && prefixReuseChecks == 2 && runtimeCallbacks == 18 && guardChecks == 42 && confirmationPositives == 6 && confirmationNegatives == 22 &&
      declarationNegatives == 72 && constTagChecks == 2 && prefixReinterpretationNegatives == 4 do
    throw (IO.userError s!"runtime bridge/guard/confirmation counts: binder={binderConfirmationNegatives} prefix={prefixReuseChecks} callbacks={runtimeCallbacks} guards={guardChecks} positive={confirmationPositives} confirmations={confirmationNegatives} declarations={declarationNegatives} const={constTagChecks} reinterpret={prefixReinterpretationNegatives}")
  IO.println s!"PASS {materialCount} material views; 9 empty-prefix Dynamic roundtrips; 18 real callbacks, 42 final-assembly guards, 6 Reify selections, 20 object residuals +2 binder residuals and 72 declaration negatives; 2 Type/Const syntax controls"
