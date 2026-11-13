import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi
import Miri.Input.WorldObjectCandidate

open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def sameArg (aWorld bWorld : TypeArena.World) (a b : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  pure ((← GenericInstantiationWorld.ofType aWorld 16384 a.layout.ty) ==
    (← GenericInstantiationWorld.ofType bWorld 16384 b.layout.ty) && a.layout.layout == b.layout.layout && a.mode == b.mode)

def main (args : List String) : IO Unit := do
  let [basePath,oraclePath] := args | throw (IO.userError "expected independent Virtual source and pinned ABI oracle")
  let decoded := (← must (decodeJson (← IO.FS.readFile basePath))).document
  let base := {decoded with types := decoded.types.map (fun node =>
    {node with compilerFacts := node.compilerFacts.map (fun facts => {facts with booleanQueries := #[],projectionQueries := none})})}
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument base).mapError toString)
  let reference ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let referenceWorld ← must ((RuntimeArrayTypes.create reference).mapError reprStr)
  let traits := base.definitions.filter fun source => source.crateIndex == 0 &&
    (source.rawPath.bind fun path => path.components.back?.bind (·.name)) == some "Generic"
  let #[trait] := traits | throw (IO.userError "novel source Generic trait not unique")
  let methods := base.definitions.zipIdx.filter fun (source,_) => source.crateIndex == 0 &&
    (source.rawPath.bind fun path => path.components.back?.bind (·.name)) == some "call"
  let #[(method,methodId)] := methods | throw (IO.userError "novel source trait method not unique")
  let rows := oracle.queries.instanceAbis.filter fun row =>
    match oracle.instances[row.instanceId]? with
    | some node => match node.instanceKind with
      | .Virtual id _ => (oracle.definitions[id]?).any fun source => source.crateIndex == method.crateIndex && source.index == method.index
      | _ => false
    | _ => false
  let #[row] := rows | throw (IO.userError "novel oracle Virtual ABI not unique")
  let some oracleInstance := oracle.instances[row.instanceId]? | throw (IO.userError "novel oracle node absent")
  let .Virtual _ oracleSlot := oracleInstance.instanceKind | throw (IO.userError "novel oracle is not Virtual")
  unless oracleSlot == 3 do throw (IO.userError "novel oracle dispatch slot differs from source first-method slot")
  unless metadata.source.producer.abiSession == reference.source.producer.abiSession do
    throw (IO.userError "novel source/oracle ABI sessions differ")
  let (arguments,created) ← must ((RuntimeArrayTypes.liftType do
    let length ← TypeArena.World.internConstant (.Value base.queries.primitives.usize ⟨#[.Leaf 5 initial.arena.pointerBytes],0⟩)
    let array ← TypeArena.World.internType (.array base.queries.primitives.u8 length)
    let dynamic ← TypeArena.World.internType (.dynamic ⟨#[⟨#[],.trait ⟨trait.crateIndex,trait.index⟩ #[.Type array]⟩],.Erased⟩)
    let receiver ← TypeArena.World.internType (.reference dynamic .Not .Erased)
    unless array >= initial.arena.typeCount && dynamic >= initial.arena.typeCount && receiver >= initial.arena.typeCount do
      throw "novel array/dyn/reference source identity was material in base"
    pure #[Miri.MIR.GenericArg.Type dynamic,.Type array]).run initial)
  unless (← must (GenericInstantiationWorld.ofArguments created.arena 16384 arguments)) ==
      (← must (GenericInstantiationWorld.ofArguments referenceWorld.arena 16384 oracleInstance.genericArgs)) do
    throw (IO.userError "novel source/oracle complete canonical arguments differ")
  let store ← must (InstanceArena.Store.ofSource created.arena #[])
  let queries := {metadata.source.queries with instanceAbis := #[],functionFacts :=
    {metadata.source.queries.functionFacts with types := #[],pointerAbis := #[],helperSignatures := #[]}}
  let stripped := {metadata.source with functionAbis := #[],queries}
  let world := {created with instances := store,bodies := BodyArena.Store.ofSource #[],metadata := {metadata with source := stripped}}
  let (callee,selected) ← must ((WorldObjectCandidate.resolveOrdinary 100000 16384 methodId arguments).run world)
  let key ← must do
    match ← selected.instances.lookup callee with | .material key | .constructed key => pure key
  unless key.kind == .Virtual methodId 3 && key.arguments == arguments do
    throw (IO.userError "novel normal source resolver changed the canonical Virtual key")
  let (actual,after) ← must ((WorldInstanceAbi.construct callee #[]).run selected)
  let expected ← must (CallResolution.functionAbiId reference row.abiId)
  unless actual.args.size == expected.args.size && actual.conv == expected.conv && actual.cVariadic == expected.cVariadic &&
    actual.fixedCount == expected.fixedCount && actual.canUnwind == expected.canUnwind &&
    (← must (sameArg after.arena referenceWorld.arena actual.ret expected.ret)) do
    throw (IO.userError "novel complete Virtual return/interface ABI differs from rustc")
  for (a,b) in actual.args.zip expected.args do
    unless ← must (sameArg after.arena referenceWorld.arena a b) do
      throw (IO.userError "novel complete Virtual argument ABI differs from rustc")
  IO.println "PASS novel array5/dyn/reference/Virtual IDs from normal source selection match complete rustc ABI; empty bodies/instances and no ABI catalogs"
