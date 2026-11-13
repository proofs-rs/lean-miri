import Miri.Input.CompilerInstanceAbi
import Miri.Input.Decoder
import Miri.Input.WorldObjectCandidate
import Miri.Input.WorldInstanceAbi

open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def sameArg (aWorld bWorld : TypeArena.World) (a b : Miri.ABI.ArgAbi TypeId) : Except String Bool := do
  pure ((← GenericInstantiationWorld.ofType aWorld 16384 a.layout.ty) ==
    (← GenericInstantiationWorld.ofType bWorld 16384 b.layout.ty) && a.layout.layout == b.layout.layout && a.mode == b.mode)
private def sameAbi (aWorld bWorld : TypeArena.World) (a b : Miri.ABI.FnAbi TypeId) : Except String Bool := do
  unless a.args.size == b.args.size && a.conv == b.conv && a.cVariadic == b.cVariadic &&
      a.fixedCount == b.fixedCount && a.canUnwind == b.canUnwind &&
      (← sameArg aWorld bWorld a.ret b.ret) do return false
  for (x,y) in a.args.zip b.args do unless ← sameArg aWorld bWorld x y do return false
  pure true

def main (args : List String) : IO Unit := do
  let [candidatePath,oraclePath] := args | throw (IO.userError "expected source Virtual candidate and pinned actual ABI oracle")
  let decoded := (← must (decodeJson (← IO.FS.readFile candidatePath))).document
  let poisonedTypes := decoded.types.map fun (node : TypeNode) =>
    let shape : TypeShape := match node.shape with
      | .adt data =>
        let variants := data.variants.map fun (variant : AdtVariant) =>
          {variant with fields := variant.fields.map (fun field => {field with typeId := decoded.queries.primitives.u8})}
        .adt {data with variants}
      | other => other
    let compilerFacts := node.compilerFacts.map (fun facts => {facts with booleanQueries := #[],projectionQueries := none,adt := none})
    {node with shape,compilerFacts}
  let document := {decoded with types := poisonedTypes}
  let oracle := (← must (decodeJson (← IO.FS.readFile oraclePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let reference ← must ((RuntimeMetadata.ofDocument oracle).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let referenceWorld ← must ((RuntimeArrayTypes.create reference).mapError reprStr)
  let queries := {metadata.source.queries with instanceAbis := #[],functionFacts :=
    {metadata.source.queries.functionFacts with types := #[],pointerAbis := #[],helperSignatures := #[]}}
  let stripped := {metadata.source with functionAbis := #[],queries}
  let empty ← must (InstanceArena.Store.ofSource initial.arena #[])
  let base := {initial with instances := empty,bodies := BodyArena.Store.ofSource #[],metadata := {metadata with source := stripped}}
  let mut checked := 0
  let mut residual := 0
  for row in oracle.queries.instanceAbis do
    let some node := oracle.instances[row.instanceId]? | throw (IO.userError "oracle node missing")
    let .Virtual definition slot := node.instanceKind | continue
    let some declaration := oracle.definitions[definition]? | throw (IO.userError "oracle method missing")
    unless declaration.crateIndex == 0 do continue
    let terms ← must (GenericInstantiationWorld.ofArguments referenceWorld.arena 16384 node.genericArgs)
    let (actualArguments,world) ← must ((RuntimeArrayTypes.liftType
      (GenericInstantiationWorld.resolveArguments 16384 terms)).run base)
    let method ← must (world.arena.definitionRef ⟨declaration.crateIndex,declaration.index⟩)
    let (callee,selected) ← must ((WorldObjectCandidate.resolveOrdinary 100000 16384 method actualArguments).run world)
    let key ← must do
      match ← selected.instances.lookup callee with | .material key | .constructed key => pure key
    unless key.kind == .Virtual method slot && key.arguments == actualArguments do
      throw (IO.userError "normal source resolver differs from complete rustc Virtual key")
    let expected ← must (CallResolution.functionAbiId reference row.abiId)
    let (actual,after) ← must ((WorldVirtualAbi.construct callee #[]).run selected)
    unless ← must (sameAbi after.arena referenceWorld.arena actual expected) do
      throw (IO.userError "complete source Virtual ABI differs from pinned rustc")
    let noLocationPrimitives := {selected.metadata.source.queries.primitives with callerLocationType := none}
    let noLocationQueries := {selected.metadata.source.queries with primitives := noLocationPrimitives}
    let noLocationSource := {selected.metadata.source with queries := noLocationQueries}
    let noLocationMetadata := {selected.metadata with source := noLocationSource,checkedMaterial := none,denseTypes := none}
    if ((WorldVirtualAbi.construct callee #[]).run {selected with metadata := noLocationMetadata}).isOk then
      throw (IO.userError "tracked ABI invented absent caller-location source")
    let wrongPrimitives := {noLocationPrimitives with callerLocationType := some document.queries.primitives.u8}
    let wrongQueries := {noLocationQueries with primitives := wrongPrimitives}
    let wrongSource := {noLocationSource with queries := wrongQueries}
    let wrongMetadata := {noLocationMetadata with source := wrongSource,checkedMaterial := none,denseTypes := none}
    if ((WorldVirtualAbi.construct callee #[]).run {selected with metadata := wrongMetadata}).isOk then
      throw (IO.userError "tracked ABI accepted nonreference caller-location source")
    let noSession := {selected with metadata := {selected.metadata with source :=
      {selected.metadata.source with producer := {selected.metadata.source.producer with abiSession := none}},checkedMaterial := none}}
    if ((WorldVirtualAbi.construct callee #[]).run noSession).isOk then
      throw (IO.userError "Virtual ABI accepted absent canonical session")
    let extra := #[metadata.source.queries.primitives.u8]
    if ((WorldVirtualAbi.construct callee extra).run selected).isOk then
      throw (IO.userError "nonvariadic Virtual accepted extra arguments")
    checked := checked + 1
  unless checked == 1 && residual == 0 do throw (IO.userError s!"Virtual coverage differs {checked}/{residual}")
  IO.println "PASS complete tracked Virtual FnAbi from source;canonical caller-location type/raw lang-item fields;missing/wrong type/session/extra controls"
