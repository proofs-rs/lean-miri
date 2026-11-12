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
  for row in oracle.queries.instanceAbis do
    let some node := oracle.instances[row.instanceId]? | throw (IO.userError "missing oracle instance")
    let .Item definition := node.instanceKind | continue
    let some source := oracle.definitions[definition]? | continue
    let some rawPath := source.rawPath | continue
    unless rawPath.components.back?.bind (·.name) == some "identity" do continue
    let key ← must (InstanceArena.Key.ofSource oracleWorld.arena node.instanceKind node.genericArgs)
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
    let world := {initial with instances := store, metadata := {runtime with source}}
    let (novel,after) ← must ((WorldInstanceAbi.construct callee #[]).run world)
    unless (← must (sameAbi after.arena oracleWorld.arena novel expected)) &&
        after.instances.constructed == world.instances.constructed do
      throw (IO.userError "constructed instance ABI used numeric material capability or lost World")
    let noPolicy := {source with definitions := source.definitions.map (fun defn => {defn with functionAbiMaterial := none})}
    let invalid := {world with metadata := {world.metadata with source := noPolicy, checkedMaterial := none}}
    if ((WorldInstanceAbi.construct callee #[]).run invalid).isOk then
      throw (IO.userError "missing raw panic/codegen policy was accepted")
    checked := checked + 1
  unless checked == 10 do throw (IO.userError s!"only {checked} raw generic scalar ABI cases compared")
  if migrated then
    let residuals := document.instances.filter fun entry =>
      match entry.instanceKind with
      | .Item definition =>
        ((document.definitions[definition]?).bind (·.rawPath) |>.bind
          (fun path => path.components.back?.bind (·.name))) == some "unused"
      | _ => false
    let #[residual] := residuals
      | throw (IO.userError "missing unique unused HRTB-argument residual instance")
    if ((WorldInstanceAbi.construct residual.id #[]).run initial).isOk then
      throw (IO.userError "unsupported HRTB argument escaped raw signature reification boundary")
    let rows := document.queries.instanceAbis.filter
      (fun row => row.instanceId == residual.id && row.extraArgumentTypes.isEmpty)
    let #[row] := rows | throw (IO.userError "unused HRTB argument lost its exact residual ABI")
    let expected ← must (CallResolution.functionAbiId runtime row.abiId)
    let prepared ← must (CompilerInstanceAbi.prepare runtime (← must (lowerProgram document)))
    let (actual,retained) ← must ((CompilerInstanceAbi.abiOfInstanceInWorld prepared residual.id #[]).run initial)
    unless ← must (sameAbi retained.arena initial.arena actual expected) do
      throw (IO.userError "material residual ABI lookup differs from its exact compiler query")
    let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
    let key ← must (InstanceArena.Key.ofSource initial.arena residual.instanceKind residual.genericArgs)
    let (id,instances) ← must (empty.intern initial.arena key)
    if ((CompilerInstanceAbi.abiOfInstanceInWorld prepared id #[]).run {initial with instances}).isOk then
      throw (IO.userError "constructed HRTB argument borrowed an unrelated material-prefix ABI")
  IO.println s!"PASS {checked} complete pinned-rustc ABI comparisons, constructed keys without result catalogs, missing policy rejection"
