import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi

/-! Fresh pinned rustc ABI correspondence, then the same complete keys outside
an empty instance prefix and with every imported ABI result removed. The optional
second input is the shadow producer that uses actual rustc ABI queries. -/
open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def sameArgument (leftWorld rightWorld : TypeArena.World)
    (left right : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  let leftType ← GenericInstantiationWorld.ofType leftWorld 16384 left.layout.ty
  let rightType ← GenericInstantiationWorld.ofType rightWorld 16384 right.layout.ty
  pure (leftType == rightType && left.layout.layout == right.layout.layout && left.mode == right.mode)

private def sameAbi (leftWorld rightWorld : TypeArena.World)
    (left right : Miri.ABI.FnAbi TypeId) : Except String Bool := do
  unless left.args.size == right.args.size && left.cVariadic == right.cVariadic &&
      left.fixedCount == right.fixedCount && left.conv == right.conv &&
      left.canUnwind == right.canUnwind do return false
  unless ← sameArgument leftWorld rightWorld left.ret right.ret do return false
  for (a,b) in left.args.zip right.args do
    unless ← sameArgument leftWorld rightWorld a b do return false
  pure true

def main (args : List String) : IO Unit := do
  let (path,oraclePath,migrated) ← match args with
    | [path] => pure (path,path,false)
    | [path,oracle] => pure (path,oracle,true)
    | _ => throw (IO.userError "expected fresh source instance ABI fixture and optional rustc oracle")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let oracleRuntime ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let oracleWorld ← must ((RuntimeArrayTypes.create oracleRuntime).mapError reprStr)
  let mut checked := 0
  let mut pointerCases := 0
  for row in oracle.queries.instanceAbis do
    let some node := oracle.instances[row.instanceId]? | throw (IO.userError "missing oracle instance")
    let .Item definition := node.instanceKind | continue
    let some source := oracle.definitions[definition]? | continue
    let some rawPath := source.rawPath | continue
    unless ["identity","mutate","shared","capture"].any
        (fun name => rawPath.components.back?.bind (·.name) == some name) do continue
    let key ← must (InstanceArena.Key.ofSource oracleWorld.arena node.instanceKind node.genericArgs)
    if let some (Miri.MIR.GenericArg.Type argument) := key.arguments[0]? then
      let kind ← must (oracleWorld.arena.shapeKind argument)
      if kind == .rawPointer || kind == .functionPointer then pointerCases := pointerCases + 1
    let arguments ← must (GenericInstantiationWorld.ofArguments oracleWorld.arena 16384 key.arguments)
    let matching ← must (document.instances.filterM fun source => do
      let candidate ← InstanceArena.Key.ofSource initial.arena source.instanceKind source.genericArgs
      if candidate.definition != key.definition then return false
      pure ((← GenericInstantiationWorld.ofArguments initial.arena 16384 candidate.arguments) == arguments))
    let #[source] := matching | throw (IO.userError "raw ABI oracle has no unique complete source instance")
    let (actual,retained) ← must ((WorldInstanceAbi.construct source.id #[]).run initial)
    let expected ← must (CallResolution.functionAbiId oracleRuntime row.abiId)
    unless ← must (sameAbi retained.arena oracleWorld.arena actual expected) do
      throw (IO.userError s!"raw ABI differs from pinned rustc for instance {source.id}")
    if migrated && document.queries.instanceAbis.any (·.instanceId == source.id) then
      throw (IO.userError "covered source instance still retains an eager ABI result")
    let store ← must (InstanceArena.Store.ofSource initial.arena #[])
    let key ← must (InstanceArena.Key.ofSource initial.arena source.instanceKind source.genericArgs)
    let (callee,store) ← must (store.intern initial.arena key)
    unless callee == 0 do throw (IO.userError "constructed ABI instance did not append densely")
    let source := {runtime.source with functionAbis := #[], queries := {runtime.source.queries with instanceAbis := #[]}}
    let world := {initial with
      instances := store
      bodies := BodyArena.Store.ofSource #[]
      metadata := {runtime with source}}
    let enabled := (document.producer.abiSession.any fun session =>
      session.optimization != .no && !session.incrementalEnabled) &&
      document.producer.freezeLangItem.isSome
    if enabled && rawPath.components.back?.bind (·.name) != some "identity" then
      if ((WorldInstanceAbi.construct callee #[]).run world).isOk then
        throw (IO.userError "constructed non-template Item ABI borrowed a material body")
      checked := checked + 1
      continue
    let (novel,after) ← must ((WorldInstanceAbi.construct callee #[]).run world)
    unless (← must (sameAbi after.arena oracleWorld.arena novel expected)) &&
        after.instances.constructed == world.instances.constructed do
      throw (IO.userError "constructed instance ABI used numeric material capability or lost World")
    if enabled then
      unless after.bodies.count == 1 do
        throw (IO.userError "constructed indirect ABI did not retain its dense source body identity")
      let (repeated,reused) ← must ((WorldInstanceAbi.construct callee #[]).run after)
      unless (← must (sameAbi reused.arena after.arena repeated novel)) &&
          reused.bodies.count == after.bodies.count do
        throw (IO.userError "repeated indirect ABI demand lost source body identity reuse")
      let missingSource := {world.metadata.source with mirTemplates := #[]}
      let missing := {world with metadata := {world.metadata with source := missingSource,checkedMaterial := none}}
      if ((WorldInstanceAbi.construct callee #[]).run missing).isOk then
        throw (IO.userError "enabled indirect deduction accepted missing optimized MIR")
      let duplicateSource := {world.metadata.source with mirTemplates := world.metadata.source.mirTemplates ++ world.metadata.source.mirTemplates}
      let duplicated := {world with metadata := {world.metadata with source := duplicateSource,checkedMaterial := none}}
      if ((WorldInstanceAbi.construct callee #[]).run duplicated).isOk then
        throw (IO.userError "enabled indirect deduction accepted ambiguous optimized MIR")
      let wrongTemplates := world.metadata.source.mirTemplates.map (fun template =>
          {template with template := {template.template with skeleton :=
            {template.template.skeleton with phase := .Runtime .Initial}}})
      let wrongSource := {world.metadata.source with mirTemplates := wrongTemplates}
      let wrongPhase := {world with metadata := {world.metadata with source := wrongSource,checkedMaterial := none}}
      if ((WorldInstanceAbi.construct callee #[]).run wrongPhase).isOk then
        throw (IO.userError "enabled indirect deduction accepted nonoptimized MIR")
      let some session := document.producer.abiSession | throw (IO.userError "missing ABI session")
      let incremental := {missing with metadata := {missing.metadata with source :=
        {missing.metadata.source with producer := {missing.metadata.source.producer with
          abiSession := some {session with incrementalEnabled := true}}}}}
      let _ ← must ((WorldInstanceAbi.construct callee #[]).run incremental)
    let noPolicy := {source with definitions := source.definitions.map (fun defn => {defn with functionAbiMaterial := none})}
    let invalid := {world with metadata := {world.metadata with source := noPolicy, checkedMaterial := none}}
    if ((WorldInstanceAbi.construct callee #[]).run invalid).isOk then
      throw (IO.userError "missing raw panic/codegen policy was accepted")
    let noSession := {world with metadata := {world.metadata with source :=
      {source with producer := {source.producer with abiSession := none}},checkedMaterial := none}}
    if ((WorldInstanceAbi.construct callee #[]).run noSession).isOk then
      throw (IO.userError "instance ABI accepted missing canonical session configuration")
    checked := checked + 1
  unless checked == 12 do throw (IO.userError s!"only {checked} raw indirect ABI cases compared")
  if migrated then
    for residualName in ["residual"] do
      let residuals := document.instances.filter fun entry =>
        match entry.instanceKind with
        | .Item definition =>
          ((document.definitions[definition]?).bind (·.rawPath) |>.bind
            (fun path => path.components.back?.bind (·.name))) == some residualName
        | _ => false
      if residualName == "reference_residual" && residuals.isEmpty then
        unless pointerCases == 0 do throw (IO.userError "pointer ABI fixture lost reference residual control")
        continue
      let #[residual] := residuals
        | throw (IO.userError "missing unique unsupported residual instance")
      if ((WorldInstanceAbi.construct residual.id #[]).run initial).isOk then
        throw (IO.userError "unsupported source signature escaped raw ABI capability boundary")
      let rows := document.queries.instanceAbis.filter
        (fun row => row.instanceId == residual.id && row.extraArgumentTypes.isEmpty)
      let #[row] := rows | throw (IO.userError "unsupported source signature lost its exact residual ABI")
      let expected ← must (CallResolution.functionAbiId runtime row.abiId)
      let prepared ← must (CompilerInstanceAbi.prepare runtime (← must (lowerProgram document)))
      let (actual,retained) ← must ((CompilerInstanceAbi.abiOfInstanceInWorld prepared residual.id #[]).run initial)
      unless ← must (sameAbi retained.arena initial.arena actual expected) do
        throw (IO.userError "material residual ABI lookup differs from its exact compiler query")
      let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
      let key ← must (InstanceArena.Key.ofSource initial.arena residual.instanceKind residual.genericArgs)
      let (id,instances) ← must (empty.intern initial.arena key)
      if ((CompilerInstanceAbi.abiOfInstanceInWorld prepared id #[]).run {initial with instances}).isOk then
        throw (IO.userError "constructed unsupported argument borrowed an unrelated material-prefix ABI")
  IO.println s!"PASS {checked} complete pinned-rustc ABI comparisons, constructed keys without result catalogs, missing policy rejection"
